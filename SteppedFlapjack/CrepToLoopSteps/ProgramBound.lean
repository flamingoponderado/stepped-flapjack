import SteppedFlapjack.CrepToLoopSteps.Branch

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Semantic and quantitative correctness for one fixed compiled program. -/
def ProgramBound {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (factor : Nat) : Prop :=
  ∀ (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code →
    crepToLoopLocalsRelExact ctxt live source.locals target.locals →
    ∃ extra targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} = (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock+extra} ≤
        factor * (CrepSteps.steps p source+1)

end SteppedFlapjack.CrepToLoopSteps
