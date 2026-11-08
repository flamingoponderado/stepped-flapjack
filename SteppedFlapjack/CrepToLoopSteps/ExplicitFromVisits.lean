import SteppedFlapjack.CrepToLoopSteps.ScalarCompilerClock
import SteppedFlapjack.CrepToLoopSteps.ScalarClockShift
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopConsumption
import SteppedFlapjack.CrepToLoopSteps.ScalarExecutable
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape

/-! Transfer a proved execution to an explicit clock and optimized code. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Given an execution and bounds on its clock padding and visits, the actual
optimizer runs at the chosen clock and its visit bound is code-computable. -/
theorem scalarLoop_explicit_optimised {F : Type} {p : HolLoopProg 64} (shape : ScalarLoop p)
    (target post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (extra budget limit : Nat)
    (run : evaluate p {target with clock := target.clock+extra} = (result,post))
    (complete : CompleteLoopResult result) (extraBound : extra ≤ budget)
    (visitBound : LoopSteps.steps p {target with clock := target.clock+extra} ≤ limit) :
    let final := {post with clock := post.clock+(budget-extra)}
    evaluate (optimiseHOL p) {target with clock := target.clock+budget} = (result,final) ∧
    LoopSteps.steps (optimiseHOL p) {target with clock := target.clock+budget} ≤
      loopVisitWeight (optimiseHOL p) * (2*limit+1) := by
  have nonTimeout : result ≠ some .timeOut := by cases complete <;> simp_all
  let delta := budget-extra
  have shifted := evaluate_add_clock_eq p _ result post delta run nonTimeout
  have clockEq : target.clock+extra+delta = target.clock+budget := by dsimp [delta]; omega
  have extended : evaluate p {target with clock := target.clock+budget} =
      (result,{post with clock := post.clock+delta}) := by simpa [clockEq] using shifted
  have count := scalarLoop_steps_add_clock shape {target with clock := target.clock+extra} post result run nonTimeout delta
  have extendedBound : LoopSteps.steps p {target with clock := target.clock+budget} ≤ limit := by
    have : LoopSteps.steps p {target with clock := target.clock+budget} =
        LoopSteps.steps p {target with clock := target.clock+extra} := by simpa [clockEq] using count
    omega
  obtain ⟨optRun,_,optBound⟩ := scalarLoop_optimise_source_steps shape _ _ result extended complete
  refine ⟨optRun,?_⟩
  exact optBound.trans (Nat.mul_le_mul_left _ (by omega))
end SteppedFlapjack.CrepToLoopSteps
