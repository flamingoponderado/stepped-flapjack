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

theorem programBound_mono {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (a b : Nat)
    (bound : @ProgramBound width _ σ p ctxt live a) (le : a ≤ b) :
    @ProgramBound width _ σ p ctxt live b := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,post,he,hs,hm,hg,hc,hl,visits⟩ :=
    bound source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  exact ⟨extra,post,he,hs,hm,hg,hc,hl,visits.trans (Nat.mul_le_mul_right _ le)⟩

end SteppedFlapjack.CrepToLoopSteps
