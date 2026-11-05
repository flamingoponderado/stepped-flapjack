import SteppedFlapjack.StackRemoveSteps.Defs

/-! Basic facts about the program-dependent factor `leafCost` for phase C3 of
stepped-flapjack#2.

`leafCost` must be at least one, because every source program takes at least one
step and the bound is `leafCost * steps`. It must also dominate the factor of
every subprogram, because the `stack_remove` correctness induction applies its
hypothesis to subprograms and then has to pay for the enclosing node's own
steps out of the parent's budget. Both facts are structural and cheap; they are
collected here so the 26 adapted case files can use them without repeating the
case analysis. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width]

/-! ### Each expansion cost is at least one -/

theorem one_le_upshiftSteps (n : Nat) : 1 ≤ upshiftSteps n := by
  rw [upshiftSteps]
  split
  · omega
  · omega

theorem one_le_downshiftSteps (n : Nat) : 1 ≤ downshiftSteps n := by
  rw [downshiftSteps]
  split
  · omega
  · omega

theorem one_le_stackFreeSteps (n : Nat) : 1 ≤ stackFreeSteps n := by
  rw [stackFreeSteps]
  split
  · omega
  · split
    · omega
    · omega

theorem one_le_stackAllocSteps (n : Nat) : 1 ≤ stackAllocSteps n := by
  rw [stackAllocSteps]
  split
  · omega
  · split
    · omega
    · omega

theorem one_le_stackStoreSteps (n : Nat) : 1 ≤ stackStoreSteps n := by
  unfold stackStoreSteps
  omega

theorem one_le_stackLoadSteps (n : Nat) : 1 ≤ stackLoadSteps n := by
  unfold stackLoadSteps
  omega

omit [NeZero width] in
theorem one_le_copyLoopSteps (B : Nat) : 1 ≤ copyLoopSteps width B := by
  unfold copyLoopSteps
  omega

omit [NeZero width] in
theorem one_le_storeConstsSteps (B : Nat) : 1 ≤ storeConstsSteps width B := by
  unfold storeConstsSteps
  omega

/-! ### The factor itself -/

theorem one_le_leafCost (B : Nat) (bounds : BitVec width × BitVec width)
    (program : HolProg width) : 1 ≤ leafCost B bounds program :=
  le_max_left _ _

/-! ### Subprogram factors are dominated by the parent's -/

theorem leafCost_seq_left (B : Nat) (bounds : BitVec width × BitVec width)
    (first second : HolProg width) :
    leafCost B bounds first ≤ leafCost B bounds (.seq first second) := by
  simp only [leafCost, rawLeafCost]
  omega

theorem leafCost_seq_right (B : Nat) (bounds : BitVec width × BitVec width)
    (first second : HolProg width) :
    leafCost B bounds second ≤ leafCost B bounds (.seq first second) := by
  simp only [leafCost, rawLeafCost]
  omega

theorem leafCost_ite_left (B : Nat) (bounds : BitVec width × BitVec width)
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width) (first second : HolProg width) :
    leafCost B bounds first ≤ leafCost B bounds (.ite cmp r ri first second) := by
  simp only [leafCost, rawLeafCost]
  omega

theorem leafCost_ite_right (B : Nat) (bounds : BitVec width × BitVec width)
    (cmp : HolCmp) (r : Nat) (ri : HolRegImm width) (first second : HolProg width) :
    leafCost B bounds second ≤ leafCost B bounds (.ite cmp r ri first second) := by
  simp only [leafCost, rawLeafCost]
  omega

theorem leafCost_loop (B : Nat) (bounds : BitVec width × BitVec width)
    (body : HolProg width) :
    leafCost B bounds body ≤ leafCost B bounds (.loop body) := by
  simp only [leafCost, rawLeafCost]
  omega

end SteppedFlapjack.StackRemoveSteps
