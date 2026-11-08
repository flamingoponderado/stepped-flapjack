import SteppedFlapjack.CrepToLoopSteps.ScalarLoopConsumption
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A related scalar compiler execution needs at most twice its visit bound
as additional clock, independently of unused source clock. -/
theorem scalarLoop_extra_le_visits {width : Nat} [NeZero width] {σ : Type} {p : CrepProgHOL width}
    (source sourcePost : CrepSemHOLState width σ) (sourceResult : Option (CrepResultHOLExact width))
    (target post : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (shape : ScalarProgram p) (extra limit : Nat)
    (sourceRun : evalCrepSemHOLProgExact source p = (sourceResult,sourcePost))
    (stateRel : crepToLoopStateRelExact source target) (postRel : crepToLoopStateRelExact sourcePost post)
    (targetRun : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} =
      (resultToLoop sourceResult,post))
    (visitBound : LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock+extra} ≤ limit) :
    extra ≤ 2*limit := by
  have loopShape := compile_scalar_program shape ctxt live
  have consumed := scalarLoop_consumed loopShape _ post (resultToLoop sourceResult) targetRun
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [sourceRun] at sourceClock
  have initial := stateRel.2.2.1
  have final := postRel.2.2.1
  simp only at consumed sourceClock
  omega

end SteppedFlapjack.CrepToLoopSteps
