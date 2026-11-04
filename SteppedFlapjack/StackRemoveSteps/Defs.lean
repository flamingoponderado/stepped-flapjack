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
  | .bitmapLoad _ _ => 7
  | .stackGetSize _ => 5
  | .stackSetSize _ => 5
  | .stackLoadAny _ _ => 5
  | .stackStoreAny _ _ => 5
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

end SteppedFlapjack.StackRemoveSteps
