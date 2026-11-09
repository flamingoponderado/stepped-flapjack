import SteppedFlapjack.StackSteps.Defs
import Flapjack.Compiler.Backend.StackRemove.Comp

/-! Adapted copy of `Flapjack/Compiler/Backend/StackRemove/Comp.lean` plus the
step-cost accounting for phase C3 of stepped-flapjack#2. This is
stepped-flapjack infrastructure with no HOL counterpart: it defines a
program-dependent factor that bounds the number of `stack_remove` target steps
per source step, together with the expansion costs of the stack operations.

The factor is the maximum, over the program's leaves, of the compiled
expansion's step count. Callees resolved from the code map at run time are
bounded separately (see the phase C3 statement); the `.call` return and handler
bodies are part of the program, so they are included. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.StackSteps
open Flapjack.StackSemControl
open Flapjack.StackSemEvaluate
open Flapjack.StackSemInst
open Flapjack.StackSemExpressions
open Flapjack.StackSemStateOps
open Flapjack.StackSemIntegerInstructions

variable {width : Nat} [NeZero width]

/-! ## Expansion step costs -/

/-- Upper bound on the number of `evaluate` invocations of the `upshift`
recursion. -/
def upshiftSteps (n : Nat) : Nat :=
  if n ≤ maxStackAlloc then 1 else 2 + upshiftSteps (n - maxStackAlloc)
termination_by n
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Upper bound on the number of `evaluate` invocations of the `downshift`
recursion. -/
def downshiftSteps (n : Nat) : Nat :=
  if n ≤ maxStackAlloc then 1 else 2 + downshiftSteps (n - maxStackAlloc)
termination_by n
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Upper bound on the number of `evaluate` invocations of `stackFree`. -/
def stackFreeSteps (n : Nat) : Nat :=
  if n = 0 then 1
  else if n ≤ maxStackAlloc then 1
  else 2 + stackFreeSteps (n - maxStackAlloc)
termination_by n
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Upper bound on the number of `evaluate` invocations of `stackAlloc`.
`singleStackAlloc` has at most four invocations (the instruction, the
`jumpLower`, and its callee, or the instruction, the `ite` and its branch). -/
def stackAllocSteps (n : Nat) : Nat :=
  if n = 0 then 1
  else if n ≤ maxStackAlloc then 6
  else 7 + stackAllocSteps (n - maxStackAlloc)
termination_by n
decreasing_by simp only [maxStackAlloc] at *; omega

/-- Upper bound on the number of `evaluate` invocations of `stackStore`. -/
def stackStoreSteps (n : Nat) : Nat :=
  3 + upshiftSteps n + downshiftSteps n

/-- Upper bound on the number of `evaluate` invocations of the `stackLoad`
branch that `comp` emits when the offset is not a small immediate: the `Seq`
node, the `moveInst`, and `stackLoad` itself. -/
def stackLoadSteps (n : Nat) : Nat :=
  6 + upshiftSteps n

/-- Upper bound on the number of `evaluate` invocations of `copyLoop` when at
most `B` bitmap words remain to be copied. One outer iteration costs the loop
and `If` nodes plus the `copyEach` body and the reload (five nodes), while
`copyEach` itself is bounded by `15 * (pattern.toNat + 1) + 3` with
`pattern.toNat < 2 ^ width`; the final exit check and trailing `copyEach`
contribute the constant. -/
def copyLoopSteps (width B : Nat) : Nat :=
  15 * B * 2 ^ width + 9 * B + 15 * 2 ^ width + 11

/-- Upper bound on the number of `evaluate` invocations of the `storeConsts`
expansion, whose prefix is five instructions and whose body is `copyLoop`. -/
def storeConstsSteps (width B : Nat) : Nat :=
  10 + copyLoopSteps width B

/-- Maximum compiled-expansion step count over the program's leaves. Callees
resolved from the code map are not counted here; they are covered by the phase
C3 statement's code-map hypothesis. -/
def rawLeafCost (B : Nat) (bounds : BitVec width × BitVec width) : HolProg width → Nat
  | .seq a b => max (rawLeafCost B bounds a) (rawLeafCost B bounds b)
  | .ite _ _ _ a b => max (rawLeafCost B bounds a) (rawLeafCost B bounds b)
  | .loop body => rawLeafCost B bounds body
  | .call ret _ handler =>
      max 1
        (max (match ret with
              | none => 0
              | some (body, _, _, _) => rawLeafCost B bounds body)
          (match handler with
           | none => 0
           | some (body, _, _) => rawLeafCost B bounds body))
  | .stackAlloc n => stackAllocSteps n
  | .stackFree n => stackFreeSteps n
  | .stackStore _ n =>
      if asmOffsetOkExact 0 bounds (wordOffset n) then 1 else stackStoreSteps n
  | .stackLoad _ n =>
      if asmOffsetOkExact 0 bounds (wordOffset n) then 1 else stackLoadSteps n
  | .storeConsts _ _ _ => storeConstsSteps width B
  | .bitmapLoad _ _ => 9
  | .stackGetSize _ => 6
  | .stackSetSize _ => 6
  | .stackLoadAny _ _ => 6
  | .stackStoreAny _ _ => 6
  | .skip => 1
  | .inst _ => 1
  | .get _ _ => 1
  | .set _ _ => 1
  | .opCurrHeap _ _ _ => 1
  | .jumpLower _ _ _ => 1
  | .alloc _ => 1
  | .raise _ => 1
  | .ret _ => 1
  | .break _ => 1
  | .continue _ => 1
  | .ffi _ _ _ _ _ _ => 1
  | .tick => 1
  | .locValue _ _ _ => 1
  | .install _ _ _ _ _ => 1
  | .shMemOp _ _ _ => 1
  | .codeBufferWrite _ _ => 1
  | .dataBufferWrite _ _ => 1
  | .rawCall _ => 1
  | .halt _ => 1

/-- Program-dependent factor bounding the `stack_remove` target steps per source
step. Every program takes at least one step, so the factor is at least one; the
`seq`, `ite`, `loop` and `call` cases take the maximum over their subprograms,
which is what lets the correctness induction thread a single factor down the
tree. -/
def leafCost (B : Nat) (bounds : BitVec width × BitVec width) (program : HolProg width) : Nat :=
  max 1 (rawLeafCost B bounds program)

/-! ## Expansion step bounds -/

variable {C F : Type}

theorem steps_inst (i : HolInst width) (s : StackSemStateFiniteExact width C F) :
    steps (.inst i, s) = 1 :=
  steps_leaf _ _ (by simp [isRecursive])

/-- A `Break` node takes one step. -/
theorem steps_break (n : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (.break n, s) = 1 := by
  change stepsHOL (.break n) s = 1
  rw [stepsHOL]
  simp
  all_goals (intro; simp)

theorem steps_skip (s : StackSemStateFiniteExact width C F) : steps (.skip, s) = 1 :=
  steps_leaf _ _ (by simp [isRecursive])

theorem steps_seq_inst_le {i : HolInst width} {b : HolProg width}
    {s : StackSemStateFiniteExact width C F} {bound : Nat}
    (hb : ∀ s' : StackSemStateFiniteExact width C F, steps (b, s') ≤ bound) :
    steps (.seq (.inst i) b, s) ≤ 2 + bound := by
  rw [steps_seq, steps_inst]
  rcases hfx : fixClock s (evaluate ((.inst i : HolProg width), s)) with ⟨res, s1⟩
  cases res with
  | none =>
    dsimp only
    have := hb s1
    omega
  | some r =>
    dsimp only
    omega

theorem steps_upshift_le (register n : Nat) :
    ∀ s : StackSemStateFiniteExact width C F, steps (upshift register n, s) ≤ upshiftSteps n := by
  induction n using upshift.induct with
  | case1 n h =>
    intro s
    rw [upshift.eq_1, if_pos h, upshiftSteps.eq_1, if_pos h]
    simp [steps_inst]
  | case2 n h ih =>
    intro s
    rw [upshift.eq_1, if_neg h, upshiftSteps.eq_1, if_neg h]
    exact steps_seq_inst_le ih

theorem steps_downshift_le (register n : Nat) :
    ∀ s : StackSemStateFiniteExact width C F, steps (downshift register n, s) ≤ downshiftSteps n := by
  induction n using downshift.induct with
  | case1 n h =>
    intro s
    rw [downshift.eq_1, if_pos h, downshiftSteps.eq_1, if_pos h]
    simp [steps_inst]
  | case2 n h ih =>
    intro s
    rw [downshift.eq_1, if_neg h, downshiftSteps.eq_1, if_neg h]
    exact steps_seq_inst_le ih

theorem steps_stackFree_le (pointer n : Nat) :
    ∀ s : StackSemStateFiniteExact width C F, steps (stackFree pointer n, s) ≤ stackFreeSteps n := by
  induction n using stackFree.induct with
  | case1 =>
    intro s
    rw [stackFree.eq_1, if_pos rfl, stackFreeSteps.eq_1, if_pos rfl]
    simp [steps_skip]
  | case2 n h0 h =>
    intro s
    rw [stackFree.eq_1, if_neg h0, if_pos h, stackFreeSteps.eq_1, if_neg h0, if_pos h]
    simp [singleStackFree, steps_inst]
  | case3 n h0 h ih =>
    intro s
    rw [stackFree.eq_1, if_neg h0, if_neg h, stackFreeSteps.eq_1, if_neg h0, if_neg h]
    rw [singleStackFree]
    exact steps_seq_inst_le ih

/-- A sequence of instructions, used to state step bounds without the
`listSeqHOL`/`map` mismatch. -/
def instSeq : List (HolInst width) → HolProg width
  | [] => .skip
  | [x] => .inst x
  | x :: y :: xs => .seq (.inst x) (instSeq (y :: xs))

theorem instSeq_eq (xs : List (HolInst width)) :
    instSeq xs = listSeqHOL (xs.map (fun i => (.inst i : HolProg width))) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simp [instSeq, listSeqHOL, ih]

/-- A sequence of instructions takes at most twice the list length. -/
theorem steps_instSeq_le (xs : List (HolInst width)) :
    ∀ s : StackSemStateFiniteExact width C F, steps (instSeq xs, s) ≤ 2 * xs.length + 1 := by
  induction xs with
  | nil =>
    intro s
    simp [instSeq, steps_skip]
  | cons x xs ih =>
    intro s
    cases xs with
    | nil =>
      simp [instSeq, steps_inst]
    | cons y ys =>
      simp only [List.length_cons]
      change steps (.seq (.inst x) (instSeq (y :: ys)), s) ≤ 2 * (ys.length + 1 + 1) + 1
      have h := steps_seq_inst_le (i := x) (s := s) ih
      simp only [List.length_cons] at h
      omega

theorem steps_bitmapLoad_le (pointer register value : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (listSeqHOL
      [.inst (.mem .load register (.addr (pointer + 1) (storeOffset .bitmapBase))),
        addInst register value, leftShiftInst register (wordShiftAmount width),
        .inst (.mem .load register (.addr register 0))], s) ≤ 9 := by
  simp only [addInst, leftShiftInst]
  change steps (instSeq
    [.mem .load register (.addr (pointer + 1) (storeOffset .bitmapBase)),
      .arith (.binop .add register register (.reg value)),
      .arith (.shift .lsl register register (.imm (BitVec.ofNat width (wordShiftAmount width)))),
      .mem .load register (.addr register 0)], s) ≤ 9
  exact steps_instSeq_le _ s

/-- A sequence of two components with state-independent bounds. -/
theorem steps_seq_le {a b : HolProg width} {s : StackSemStateFiniteExact width C F} {ba bb : Nat}
    (ha : ∀ s' : StackSemStateFiniteExact width C F, steps (a, s') ≤ ba)
    (hb : ∀ s' : StackSemStateFiniteExact width C F, steps (b, s') ≤ bb) :
    steps (.seq a b, s) ≤ 1 + ba + bb := by
  rw [steps_seq]
  have h1 := ha s
  rcases hfx : fixClock s (evaluate (a, s)) with ⟨res, s1⟩
  cases res with
  | none =>
    dsimp only
    have h2 := hb s1
    omega
  | some r =>
    dsimp only
    omega

theorem steps_stackStore_le (address register count : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (stackStore address register count, s) ≤
      3 + upshiftSteps count + downshiftSteps count := by
  have hup : ∀ s' : StackSemStateFiniteExact width C F,
      steps (upshift address count, s') ≤ upshiftSteps count :=
    steps_upshift_le (width := width) address count
  have hdown : ∀ s' : StackSemStateFiniteExact width C F,
      steps (downshift address count, s') ≤ downshiftSteps count :=
    steps_downshift_le (width := width) address count
  have hstore : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .store register (.addr address 0)), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (.inst (.mem .store register (.addr address 0)))
        (downshift address count), s') ≤ 1 + 1 + downshiftSteps count := by
    intro s'; exact steps_seq_le hstore hdown
  have houter := steps_seq_le (s := s) hup hinner
  rw [stackStore]
  omega

theorem steps_stackLoad_le (register count : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (stackLoad register count, s) ≤ 4 + upshiftSteps count := by
  have hup : ∀ s' : StackSemStateFiniteExact width C F,
      steps (upshift register count, s') ≤ upshiftSteps count :=
    steps_upshift_le (width := width) register count
  have hload : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .load register (.addr register 0)), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (upshift register count) (.inst (.mem .load register (.addr register 0))), s') ≤
        1 + upshiftSteps count + 1 := by
    intro s'; exact steps_seq_le hup hload
  have h := hinner s
  rw [stackLoad]
  omega

theorem steps_stackGetSize_le (register pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (.seq (.seq (moveInst register pointer) (subInst register (pointer + 1)))
      (rightShiftInst register (wordShiftAmount width)), s) ≤ 6 := by
  have hmove : ∀ s' : StackSemStateFiniteExact width C F,
      steps (moveInst register pointer, s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hsub : ∀ s' : StackSemStateFiniteExact width C F,
      steps (subInst register (pointer + 1), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hshift : ∀ s' : StackSemStateFiniteExact width C F,
      steps (rightShiftInst register (wordShiftAmount width), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (moveInst register pointer) (subInst register (pointer + 1)), s') ≤ 3 := by
    intro s'; exact steps_seq_le hmove hsub
  have houter := steps_seq_le (s := s) hinner hshift
  omega

theorem steps_stackSetSize_le (register pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (.seq (leftShiftInst register (wordShiftAmount width))
      (.seq (moveInst pointer (pointer + 1)) (addInst pointer register)), s) ≤ 6 := by
  have hshift : ∀ s' : StackSemStateFiniteExact width C F,
      steps (leftShiftInst register (wordShiftAmount width), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hmove : ∀ s' : StackSemStateFiniteExact width C F,
      steps (moveInst pointer (pointer + 1), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hadd : ∀ s' : StackSemStateFiniteExact width C F,
      steps (addInst pointer register, s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (moveInst pointer (pointer + 1)) (addInst pointer register), s') ≤ 3 := by
    intro s'; exact steps_seq_le hmove hadd
  have houter := steps_seq_le (s := s) hshift hinner
  omega

theorem steps_stackLoadAny_le (register index pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (.seq (.seq (moveInst register index) (addInst register pointer))
      (.inst (.mem .load register (.addr register 0))), s) ≤ 6 := by
  have hmove : ∀ s' : StackSemStateFiniteExact width C F,
      steps (moveInst register index, s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hadd : ∀ s' : StackSemStateFiniteExact width C F,
      steps (addInst register pointer, s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hload : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .load register (.addr register 0)), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (moveInst register index) (addInst register pointer), s') ≤ 3 := by
    intro s'; exact steps_seq_le hmove hadd
  have houter := steps_seq_le (s := s) hinner hload
  omega

theorem steps_stackStoreAny_le (register index pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (.seq (.inst (.arith (.binop .add pointer pointer (.reg index))))
      (.seq (.inst (.mem .store register (.addr pointer 0)))
        (.inst (.arith (.binop .sub pointer pointer (.reg index))))), s) ≤ 6 := by
  have hadd : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.arith (.binop .add pointer pointer (.reg index))), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hstore : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .store register (.addr pointer 0)), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hsub : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.arith (.binop .sub pointer pointer (.reg index))), s') ≤ 1 := by
    intro s'; exact Nat.le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (.inst (.mem .store register (.addr pointer 0)))
        (.inst (.arith (.binop .sub pointer pointer (.reg index)))), s') ≤ 3 := by
    intro s'; exact steps_seq_le hstore hsub
  have houter := steps_seq_le (s := s) hadd hinner
  omega

theorem steps_halt (n : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (.halt n, s) = 1 :=
  steps_leaf _ _ (by simp [isRecursive])

/-- The `sub` instruction used by `singleStackAlloc` preserves the code map. -/
theorem instHOL_sub_code (pointer n : Nat) {s t : StackSemStateFiniteExact width C F}
    (h : instHOL (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) s = some t) :
    t.code = s.code := by
  have cov := instHOL_coverage (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) s
  rw [h] at cov
  simp only [instInteger] at cov
  simp only [Option.some.injEq] at cov
  split at cov
  · simp_all
  · simp only [assign] at cov
    split at cov
    · simp at cov
    · simp only [Option.some.injEq] at cov
      subst cov
      simp [setVar]

theorem steps_haltInst_le (value : BitVec width) (s : StackSemStateFiniteExact width C F) :
    steps (haltInst value, s) ≤ 3 := by
  rw [haltInst, steps_seq, steps_inst]
  rcases hfx : fixClock s (evaluate ((.inst (.const 1 value) : HolProg width), s)) with ⟨res, s1⟩
  cases res with
  | none =>
    dsimp only
    have h := steps_halt 1 s1
    omega
  | some r =>
    dsimp only
    omega

theorem steps_jumpLower_stackErrLab_le (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F)
    (halt : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2))) :
    steps ((.jumpLower r1 r2 stackErrLab : HolProg width), s) ≤ 4 := by
  rw [steps_jumpLower]
  have h : (match getVar r1 s, getVar r2 s with
      | some (.word x), some (.word y) =>
          if wordCmpHOL .lower x y then
            match findCode (.inl stackErrLab) s.regs s.code with
            | some prog => if s.clock = 0 then 0 else steps (prog, decClock s)
            | none => 0
          else 0
      | _, _ => 0) ≤ 3 := by
    rcases hx : getVar r1 s with _ | x
    · simp
    · rcases hy : getVar r2 s with _ | y
      · simp
      · rcases x with xw | _
        · rcases y with yw | _
          · rw [findCode, halt]
            dsimp only
            by_cases hc : wordCmpHOL .lower xw yw
            · rw [if_pos hc]
              by_cases h0 : s.clock = 0
              · simp [h0]
              · rw [if_neg h0]
                exact steps_haltInst_le _ _
            · rw [if_neg hc]
              simp
          · simp
        · simp
  exact Nat.add_le_add_left h 1

theorem steps_ite_halt_le (r : Nat) (ri : HolRegImm width)
    (s : StackSemStateFiniteExact width C F) :
    steps (.ite .lower r ri (haltInst (2 : BitVec width)) .skip, s) ≤ 4 := by
  rw [steps_ite]
  have h : (match getVar r s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
      | some x, some y =>
          match wordSemWordCmp .lower x y with
          | some true => steps (haltInst (2 : BitVec width), s)
          | some false => steps (.skip, s)
          | none => 0
      | _, _ => 0) ≤ 3 := by
    split
    · split
      · have := steps_haltInst_le (2 : BitVec width) s
        omega
      · have := steps_skip s
        omega
      · omega
    · omega
  exact Nat.add_le_add_left h 1

theorem steps_singleStackAlloc_le (jump : Bool) (pointer n : Nat)
    (s : StackSemStateFiniteExact width C F)
    (halt : sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2))) :
    steps (singleStackAlloc jump pointer n, s) ≤ 6 := by
  rw [singleStackAlloc]
  split
  · rename_i hj
    rw [steps_seq, steps_inst]
    rcases hfx : fixClock s (evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s)) with ⟨res, s1⟩
    cases res with
    | none =>
      dsimp only
      have hs1 : s1.code = s.code := by
        rcases hev : evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s) with ⟨r, s'⟩
        rw [hev] at hfx
        simp only [fixClock, Prod.mk.injEq] at hfx
        obtain ⟨hr, hs⟩ := hfx
        subst r
        have hinst : instHOL (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) s = some s' := by
          rw [evaluate_inst] at hev
          split at hev
          · rename_i s'' hinst'
            simp only [Prod.mk.injEq] at hev
            obtain ⟨-, hs'⟩ := hev
            rw [hs'] at hinst'
            exact hinst'
          · simp at hev
        rw [← hs]
        simp [instHOL_sub_code pointer n hinst]
      have halt' : sptLookup stackErrLab s1.code = some (haltInst (BitVec.ofNat width 2)) := by
        rw [hs1]; exact halt
      have hjump := steps_jumpLower_stackErrLab_le pointer (pointer + 1) s1 halt'
      omega
    | some r =>
      dsimp only
      omega
  · rename_i hj
    rw [steps_seq, steps_inst]
    rcases hfx : fixClock s (evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s)) with ⟨res, s1⟩
    cases res with
    | none =>
      dsimp only
      have hite := steps_ite_halt_le pointer (.reg (pointer + 1)) s1
      omega
    | some r =>
      dsimp only
      omega

theorem evaluate_haltInst_some (value : BitVec width) (s : StackSemStateFiniteExact width C F) :
    ∃ (r : StackSemResult width) (t : StackSemStateFiniteExact width C F),
      evaluate (haltInst value, s) = (some r, t) := by
  rw [haltInst, evaluate_seq]
  split
  · rw [evaluate_halt]
    split <;> exact ⟨_, _, rfl⟩
  · rename_i x res' s1' hne heq
    cases res' with
    | none => exact absurd rfl hne
    | some r => exact ⟨r, s1', rfl⟩

theorem evaluate_jumpLower_stackErrLab_none {r1 r2 : Nat}
    {s t : StackSemStateFiniteExact width C F}
    (halt : sptLookup stackErrLab s.code = some (haltInst (2 : BitVec width)))
    (h : evaluate ((.jumpLower r1 r2 stackErrLab : HolProg width), s) = (none, t)) : t = s := by
  rw [evaluate_jumpLower] at h
  split at h
  · split at h
    · rw [findCode, halt] at h
      split at h
      · simp at h
      · rename_i x prog heq
        split at h
        · simp at h
        · rename_i hclock
          obtain ⟨r, t', hev⟩ := evaluate_haltInst_some (2 : BitVec width) (decClock s)
          have hprog : prog = haltInst (2 : BitVec width) := by
            simpa using heq.symm
          rw [hprog] at h
          rw [hev] at h
          dsimp only at h
          split at h <;> simp_all
    · simpa using h.symm
  · simp at h

theorem evaluate_inst_sub_code (pointer n : Nat)
    {s t : StackSemStateFiniteExact width C F}
    (h : evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s) =
      (none, t)) : t.code = s.code := by
  rw [evaluate_inst] at h
  split at h
  · rename_i s' hinst
    simp only [Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact instHOL_sub_code pointer n hinst
  · simp at h

theorem evaluate_ite_halt_skip_none {r : Nat} {ri : HolRegImm width}
    {s t : StackSemStateFiniteExact width C F}
    (h : evaluate ((.ite .lower r ri (haltInst (2 : BitVec width)) .skip : HolProg width), s) =
      (none, t)) : t = s := by
  rw [evaluate_ite] at h
  split at h
  · split at h
    · obtain ⟨r', t', hev⟩ := evaluate_haltInst_some (2 : BitVec width) s
      rw [hev] at h
      simp at h
    · simp [evaluate_skip] at h
      exact h.symm
    · simp at h
  · simp at h

theorem fixClock_inst_sub_code (pointer n : Nat) {s s1 : StackSemStateFiniteExact width C F}
    (hfx : fixClock s (evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s)) =
      (none, s1)) : s1.code = s.code := by
  rcases hev : evaluate ((.inst (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) : HolProg width), s) with ⟨r, s'⟩
  rw [hev] at hfx
  simp only [fixClock, Prod.mk.injEq] at hfx
  obtain ⟨hr, hs⟩ := hfx
  subst r
  have hinst : instHOL (.arith (.binop .sub pointer pointer (.imm (wordOffset n)))) s = some s' := by
    rw [evaluate_inst] at hev
    split at hev
    · rename_i s'' hinst'
      simp only [Prod.mk.injEq] at hev
      obtain ⟨-, hs'⟩ := hev
      rw [hs'] at hinst'
      exact hinst'
    · simp at hev
  rw [← hs]
  simp [instHOL_sub_code pointer n hinst]

theorem evaluate_singleStackAlloc_none_code (jump : Bool) (pointer n : Nat)
    {s t : StackSemStateFiniteExact width C F}
    (halt : sptLookup stackErrLab s.code = some (haltInst (2 : BitVec width)))
    (h : evaluate (singleStackAlloc jump pointer n, s) = (none, t)) : t.code = s.code := by
  rw [singleStackAlloc] at h
  split at h
  · rw [evaluate_seq] at h
    split at h
    · rename_i s1 hfx
      have hs1 : s1.code = s.code := fixClock_inst_sub_code pointer n hfx
      have halt' : sptLookup stackErrLab s1.code = some (haltInst (2 : BitVec width)) := by
        rw [hs1]; exact halt
      have ht : t = s1 := evaluate_jumpLower_stackErrLab_none halt' h
      rw [ht]; exact hs1
    · simp_all
  · rw [evaluate_seq] at h
    split at h
    · rename_i s1 hfx
      have hs1 : s1.code = s.code := fixClock_inst_sub_code pointer n hfx
      have ht : t = s1 := evaluate_ite_halt_skip_none h
      rw [ht]; exact hs1
    · simp_all

theorem steps_stackAlloc_le (jump : Bool) (pointer n : Nat) :
    ∀ s : StackSemStateFiniteExact width C F,
      sptLookup stackErrLab s.code = some (haltInst (2 : BitVec width)) →
      steps (stackAlloc jump pointer n, s) ≤ stackAllocSteps n := by
  induction n using stackAlloc.induct with
  | case1 =>
    intro s halt
    rw [stackAlloc.eq_1, if_pos rfl, stackAllocSteps.eq_1, if_pos rfl]
    rw [steps_skip (width := width) s]
  | case2 n h0 h =>
    intro s halt
    rw [stackAlloc.eq_1, if_neg h0, if_pos h, stackAllocSteps.eq_1, if_neg h0, if_pos h]
    exact steps_singleStackAlloc_le jump pointer n s halt
  | case3 n h0 h ih =>
    intro s halt
    rw [stackAlloc.eq_1, if_neg h0, if_neg h, stackAllocSteps.eq_1, if_neg h0, if_neg h]
    rw [steps_seq]
    have hsingle := steps_singleStackAlloc_le jump pointer maxStackAlloc s halt
    rcases hfx : fixClock s (evaluate (singleStackAlloc jump pointer maxStackAlloc, s)) with ⟨res, s1⟩
    cases res with
    | none =>
      dsimp only
      have hs1code : s1.code = s.code := by
        rcases hev : evaluate (singleStackAlloc jump pointer maxStackAlloc, s) with ⟨r, s'⟩
        rw [hev] at hfx
        simp only [fixClock, Prod.mk.injEq] at hfx
        obtain ⟨hr, hs⟩ := hfx
        subst r
        have hcode : s'.code = s.code :=
          evaluate_singleStackAlloc_none_code jump pointer maxStackAlloc halt hev
        rw [← hs]
        simp [hcode]
      have halt' : sptLookup stackErrLab s1.code = some (haltInst (2 : BitVec width)) := by
        rw [hs1code]; exact halt
      have hrec := ih s1 halt'
      omega
    | some r =>
      dsimp only
      omega

theorem steps_ite_skip_add_le (r : Nat) (ri : HolRegImm width) (temporary : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (.ite .test r ri .skip (addInst temporary 3), s) ≤ 2 := by
  rw [steps_ite]
  have h : (match getVar r s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
      | some x, some y =>
          match wordSemWordCmp .test x y with
          | some true => steps (.skip, s)
          | some false => steps (addInst temporary 3, s)
          | none => 0
      | _, _ => 0) ≤ 1 := by
    split
    · split
      · have := steps_skip s; omega
      · have := steps_inst (.arith (.binop .add temporary temporary (.reg 3))) s
        simp only [addInst] at this ⊢
        omega
      · omega
    · omega
  exact Nat.add_le_add_left h 1

/-- The sentinel run of `copyEach` (pattern register equal to 1) takes three steps. -/
theorem steps_copyEach_sentinel {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (s : StackSemStateFiniteExact width C F)
    (h : StackSemStateOps.getVar 1 s = some (.word (BitVec.ofNat width 1))) :
    steps (copyEach temporary bitmap, s) ≤ 3 := by
  have hdef : (copyEach temporary bitmap : HolProg width)
      = (.loop (.ite .notEqual 1 (.imm 1)
          (listSeqHOL [loadInst temporary bitmap, addBytesInWordInst bitmap,
            .ite .test 1 (.imm 1) .skip (addInst temporary 3),
            rightShiftInst 1 1, storeInst temporary 2, addBytesInWordInst 2])
          (.break 0) : HolProg width)) := rfl
  rw [hdef, steps_loop, steps_ite]
  rw [h]
  simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    Compiler.Encoders.Asm.wordCmpHOL]
  simp
  rw [evaluate_ite]
  rw [h]
  simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
    Compiler.Encoders.Asm.wordCmpHOL]
  simp
  rw [evaluate_break]
  simp only [fixClock, StackSemControl.contLoop]
  rw [steps_break]
  simp

theorem steps_innerBody_le (temporary bitmap : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (listSeqHOL [loadInst temporary bitmap, addBytesInWordInst bitmap,
      .ite .test 1 (.imm 1) .skip (addInst temporary 3), rightShiftInst 1 1,
      storeInst temporary 2, addBytesInWordInst 2], s) ≤ 12 := by
  have h1 : ∀ s' : StackSemStateFiniteExact width C F, steps (loadInst temporary bitmap, s') ≤ 1 := by
    intro s'; simp only [loadInst]; exact Nat.le_of_eq (steps_inst _ s')
  have h2 : ∀ s' : StackSemStateFiniteExact width C F, steps (addBytesInWordInst bitmap, s') ≤ 1 := by
    intro s'; simp only [addBytesInWordInst]; exact Nat.le_of_eq (steps_inst _ s')
  have h3 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.ite .test 1 (.imm 1) .skip (addInst temporary 3), s') ≤ 2 :=
    fun s' => steps_ite_skip_add_le 1 (.imm 1) temporary s'
  have h4 : ∀ s' : StackSemStateFiniteExact width C F, steps (rightShiftInst 1 1, s') ≤ 1 := by
    intro s'; simp only [rightShiftInst]; exact Nat.le_of_eq (steps_inst _ s')
  have h5 : ∀ s' : StackSemStateFiniteExact width C F, steps (storeInst temporary 2, s') ≤ 1 := by
    intro s'; simp only [storeInst]; exact Nat.le_of_eq (steps_inst _ s')
  have h6 : ∀ s' : StackSemStateFiniteExact width C F, steps (addBytesInWordInst 2, s') ≤ 1 := by
    intro s'; simp only [addBytesInWordInst]; exact Nat.le_of_eq (steps_inst _ s')
  have h56 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (storeInst temporary 2) (addBytesInWordInst 2), s') ≤ 3 := by
    intro s'; exact steps_seq_le h5 h6
  have h456 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (rightShiftInst 1 1) (.seq (storeInst temporary 2) (addBytesInWordInst 2)), s') ≤ 5 := by
    intro s'; exact steps_seq_le h4 h56
  have h3456 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (.ite .test 1 (.imm 1) .skip (addInst temporary 3))
        (.seq (rightShiftInst 1 1) (.seq (storeInst temporary 2) (addBytesInWordInst 2))), s') ≤ 8 := by
    intro s'; exact steps_seq_le h3 h456
  have h23456 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (addBytesInWordInst bitmap)
        (.seq (.ite .test 1 (.imm 1) .skip (addInst temporary 3))
          (.seq (rightShiftInst 1 1) (.seq (storeInst temporary 2) (addBytesInWordInst 2)))), s') ≤ 10 := by
    intro s'; exact steps_seq_le h2 h3456
  have h123456 := steps_seq_le (s := s) h1 h23456
  simpa only [listSeqHOL] using h123456


end SteppedFlapjack.StackRemoveSteps
