import SteppedFlapjack.StackRemoveSteps.CompCorrect.FiniteAssembly
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompileSemantics
namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- Stack removal simulates a bounded entry run with its computed finite-code
and finite-oracle factor, preserving the complete FFI state. -/
theorem entryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock n : Nat)
    (source target post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (hsteps : steps (.call none (.inl start) none, {source with clock := clock}) ≤ n) :
    ∃ extra postTarget, evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = post.ffi ∧
      steps (.call none (.inl start) none, {target with clock := extra + clock}) ≤
        computedRunCost bounds n (.call none (.inl start) none) source * n := by
  obtain ⟨extra, postTarget, targetRun, postRelation, cost⟩ :=
    compCorrectWithinStepsComputed (.call none (.inl start) none) {source with clock := clock}
      result post {target with clock := clock} pointer bounds jump n hsteps
      ⟨run, nonError, RelationLaws.stateRelWithClock jump bounds pointer clock source target relation,
        by simp [StackProps.regBound]⟩
  refine ⟨extra, postTarget, ?_, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact (RelationLaws.stateRelConst jump bounds pointer post postTarget postRelation).2.2.2.2.1
    | some value =>
      cases value
      all_goals first
        | exact postRelation
        | exact (RelationLaws.stateRelConst jump bounds pointer post postTarget postRelation).2.2.2.2.1
  · simpa only [comp, computedRunCost, initialBitmapBudget, initialRunCost, initialCodeOracleCost,
      codeCost, oraclePrefixCost, oracleBitmapBudget] using cost
end SteppedFlapjack.StackRemoveSteps
