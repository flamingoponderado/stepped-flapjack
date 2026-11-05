import SteppedFlapjack.StackRemoveSteps.LeafCostBounds
import Flapjack.Compiler.Backend.StackRemove.Comp

/-! Leaf step bounds for phase C3 of stepped-flapjack#2.

For every leaf node with a nontrivial expansion, the compiled form takes at
most `leafCost B bounds` steps from any state. Together with `steps_leaf`, which
gives exactly one step for the leaves that `comp` leaves alone, these cover the
28 non-recursive constructors of the top-level induction. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width]
variable {C F : Type}

theorem steps_comp_stackFree_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer n B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackFree n), s) ≤ leafCost B bounds (.stackFree n) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackFree_le pointer n s) (le_max_right _ _)

theorem steps_comp_stackAlloc_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer n B : Nat) (s : StackSemStateFiniteExact width C F)
    (haltCode : sptLookup stackErrLab s.code = some (haltInst (2 : BitVec width))) :
    steps (comp jump bounds pointer (.stackAlloc n), s) ≤ leafCost B bounds (.stackAlloc n) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackAlloc_le jump pointer n s haltCode) (le_max_right _ _)

theorem steps_comp_stackStore_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register n B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackStore register n), s) ≤
      leafCost B bounds (.stackStore register n) := by
  simp only [comp, leafCost, rawLeafCost]
  by_cases ok : asmOffsetOkExact 0 bounds (wordOffset n)
  · rw [if_pos ok, if_pos ok]
    exact le_trans (le_of_eq (steps_inst _ s)) (le_max_right _ _)
  · rw [if_neg ok, if_neg ok]
    exact le_trans (steps_stackStore_le pointer register n s) (le_max_right _ _)

theorem steps_comp_stackLoad_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register n B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackLoad register n), s) ≤
      leafCost B bounds (.stackLoad register n) := by
  simp only [comp, leafCost, rawLeafCost]
  by_cases ok : asmOffsetOkExact 0 bounds (wordOffset n)
  · rw [if_pos ok, if_pos ok]
    exact le_trans (le_of_eq (steps_inst _ s)) (le_max_right _ _)
  · rw [if_neg ok, if_neg ok]
    have ha : ∀ s' : StackSemStateFiniteExact width C F, steps (moveInst register pointer, s') ≤ 1 :=
      fun s' => le_of_eq (steps_inst _ s')
    have hb : ∀ s' : StackSemStateFiniteExact width C F,
        steps (stackLoad register n, s') ≤ 4 + upshiftSteps n :=
      fun s' => steps_stackLoad_le register n s'
    have hseq : steps (.seq (moveInst register pointer) (stackLoad register n), s) ≤
        6 + upshiftSteps n := by
      have h := steps_seq_le (s := s) ha hb
      omega
    rw [stackLoadSteps]
    exact le_trans hseq (le_max_right _ _)

theorem steps_comp_stackGetSize_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackGetSize register), s) ≤
      leafCost B bounds (.stackGetSize register) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackGetSize_le register pointer s) (le_max_right _ _)

theorem steps_comp_stackSetSize_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackSetSize register), s) ≤
      leafCost B bounds (.stackSetSize register) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackSetSize_le register pointer s) (le_max_right _ _)

theorem steps_comp_stackLoadAny_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register index B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackLoadAny register index), s) ≤
      leafCost B bounds (.stackLoadAny register index) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackLoadAny_le register index pointer s) (le_max_right _ _)

theorem steps_comp_stackStoreAny_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register index B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.stackStoreAny register index), s) ≤
      leafCost B bounds (.stackStoreAny register index) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_stackStoreAny_le register index pointer s) (le_max_right _ _)

theorem steps_comp_bitmapLoad_le (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer register value B : Nat) (s : StackSemStateFiniteExact width C F) :
    steps (comp jump bounds pointer (.bitmapLoad register value), s) ≤
      leafCost B bounds (.bitmapLoad register value) := by
  simp only [comp, leafCost, rawLeafCost]
  exact le_trans (steps_bitmapLoad_le pointer register value s) (le_max_right _ _)

end SteppedFlapjack.StackRemoveSteps
