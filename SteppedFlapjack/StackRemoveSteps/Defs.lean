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
branch that `comp` emits when the offset is not a small immediate. -/
def stackLoadSteps (n : Nat) : Nat :=
  4 + upshiftSteps n

/-- Upper bound on the number of `evaluate` invocations of `copyLoop` when the
runtime bitmap word count is at most `B`. The loop copies one bitmap word per
outer iteration and one bit per inner iteration, so the bound is quadratic in
the word width. -/
def copyLoopSteps (width B : Nat) : Nat :=
  14 * B * (width + 1) + 28

/-- Upper bound on the number of `evaluate` invocations of the `storeConsts`
expansion, whose prefix is five instructions and whose body is `copyLoop`. -/
def storeConstsSteps (width B : Nat) : Nat :=
  10 + copyLoopSteps width B

/-- Program-dependent factor: the maximum compiled-expansion step count over
the program's leaves. Callees resolved from the code map are not counted here;
they are covered by the phase C3 statement's code-map hypothesis. -/
def leafCost (B : Nat) (bounds : BitVec width × BitVec width) : HolProg width → Nat
  | .seq a b => max (leafCost B bounds a) (leafCost B bounds b)
  | .ite _ _ _ a b => max (leafCost B bounds a) (leafCost B bounds b)
  | .loop body => leafCost B bounds body
  | .call ret _ handler =>
      max 1
        (max (match ret with
              | none => 0
              | some (body, _, _, _) => leafCost B bounds body)
          (match handler with
           | none => 0
           | some (body, _, _) => leafCost B bounds body))
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
  | _ => 1



/-! ## Expansion step bounds -/

variable {C F : Type}

theorem steps_inst (i : HolInst width) (s : StackSemStateFiniteExact width C F) :
    steps (.inst i, s) = 1 :=
  steps_leaf _ _ (by simp [isRecursive])

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
    intro s'; exact le_of_eq (steps_inst _ s')
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
    intro s'; exact le_of_eq (steps_inst _ s')
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
    intro s'; exact le_of_eq (steps_inst _ s')
  have hsub : ∀ s' : StackSemStateFiniteExact width C F,
      steps (subInst register (pointer + 1), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
  have hshift : ∀ s' : StackSemStateFiniteExact width C F,
      steps (rightShiftInst register (wordShiftAmount width), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
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
    intro s'; exact le_of_eq (steps_inst _ s')
  have hmove : ∀ s' : StackSemStateFiniteExact width C F,
      steps (moveInst pointer (pointer + 1), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
  have hadd : ∀ s' : StackSemStateFiniteExact width C F,
      steps (addInst pointer register, s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
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
    intro s'; exact le_of_eq (steps_inst _ s')
  have hadd : ∀ s' : StackSemStateFiniteExact width C F,
      steps (addInst register pointer, s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
  have hload : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .load register (.addr register 0)), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
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
    intro s'; exact le_of_eq (steps_inst _ s')
  have hstore : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.mem .store register (.addr pointer 0)), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
  have hsub : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.inst (.arith (.binop .sub pointer pointer (.reg index))), s') ≤ 1 := by
    intro s'; exact le_of_eq (steps_inst _ s')
  have hinner : ∀ s' : StackSemStateFiniteExact width C F,
      steps (.seq (.inst (.mem .store register (.addr pointer 0)))
        (.inst (.arith (.binop .sub pointer pointer (.reg index)))), s') ≤ 3 := by
    intro s'; exact steps_seq_le hstore hsub
  have houter := steps_seq_le (s := s) hadd hinner
  omega

end SteppedFlapjack.StackRemoveSteps
