import SteppedFlapjack.StackAllocSteps.CollectorStructural
import Flapjack.Compiler.Backend.StackRemove.InitCode
namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

/-- Programs with no recursive evaluation except structural sequence/branch. -/
def straightLine : HolProg width → Bool
  | .seq a b => straightLine a && straightLine b
  | .ite _ _ _ a b => straightLine a && straightLine b
  | .loop _ | .jumpLower _ _ _ | .rawCall _ | .call _ _ _ => false
  | _ => true

theorem straightLineLoopOnly (p : HolProg width) (h : straightLine p = true) : loopOnly p = true := by
  cases hp : p <;> simp_all [straightLine, loopOnly]
  case seq a b => exact ⟨straightLineLoopOnly a h.1, straightLineLoopOnly b h.2⟩
  case ite cmp r ri a b => exact ⟨straightLineLoopOnly a h.1, straightLineLoopOnly b h.2⟩
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

theorem straightLineCostClock (p : HolProg width) (h : straightLine p = true) (k : Nat) :
    loopOnlyCost k p = loopOnlyCost 0 p := by
  cases hp : p <;> simp_all [straightLine, loopOnlyCost]
  case seq a b => rw [straightLineCostClock a h.1 k, straightLineCostClock b h.2 k]
  case ite cmp r ri a b => rw [straightLineCostClock a h.1 k, straightLineCostClock b h.2 k]
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- A straight-line program has a structural bound independent of its clock. -/
theorem straightLineSteps {C F : Type} (p : HolProg width) (h : straightLine p = true)
    (s : StackSemStateFiniteExact width C F) : steps (p, s) ≤ loopOnlyCost 0 p := by
  have hb := loopOnlyCostBound (C := C) (F := F) s.clock p (straightLineLoopOnly p h) s (Nat.le_refl _)
  rw [straightLineCostClock p h s.clock] at hb
  exact hb

theorem straightLineStoreList (addr tmp : Nat) (xs : List (Sum (BitVec width) Nat)) :
    straightLine (storeListCode addr tmp xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [storeListCode, listSeqHOL, straightLine, addBytesInWordInst, ih]

/-- The generated stack-removal initializer has no loops or calls. -/
theorem straightLineInitCode (gen : Bool) (maxHeap pointer : Nat) :
    straightLine (initCode (width := width) gen maxHeap pointer) = true := by
  simp [initCode, initMemory, listSeqHOL, straightLine, straightLineStoreList,
    moveHOL, subInst, addInst, rightShiftInst, leftShiftInst, constInst, loadInst,
    storeInst, addBytesInWordInst]

/-- The generated initialization code takes a fixed, computable number of steps. -/
theorem initCodeSteps {C F : Type} (gen : Bool) (maxHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps (initCode gen maxHeap pointer, s) ≤ loopOnlyCost 0 (initCode gen maxHeap pointer : HolProg width) :=
  straightLineSteps _ (straightLineInitCode gen maxHeap pointer) s

/-- The initialization entry adds only its fixed structural cost and two
control steps before executing the actual program entry. -/
theorem initEntrySteps {C F : Type} (gen : Bool) (maxHeap pointer start : Nat)
    (s post : StackSemStateFiniteExact width C F)
    (entry : sptLookup 0 s.code = some (.seq (initCode gen maxHeap pointer) (.call none (.inl start) none)))
    (nonzero : s.clock ≠ 0)
    (run : evaluate (initCode gen maxHeap pointer, decClock s) = (none, post)) :
    steps (.call none (.inl 0) none, s) ≤
      2 + loopOnlyCost 0 (initCode gen maxHeap pointer : HolProg width) +
        steps (.call none (.inl start) none, post) := by
  rw [steps_call_none]
  simp only [findCode, entry, if_neg nonzero]
  rw [steps_seq_run _ _ _ _ run]
  have bound := initCodeSteps gen maxHeap pointer (decClock s)
  omega

end SteppedFlapjack.StackRemoveSteps
