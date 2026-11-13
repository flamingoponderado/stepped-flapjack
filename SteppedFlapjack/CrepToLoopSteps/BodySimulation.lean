import SteppedFlapjack.CrepToLoopSteps.ProgramBound
import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock

/-! Internal interfaces for compositional loop-body simulation. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A body execution can be reproduced with padding bounded by a function of
its source visits. The interface is discharged by the results below. -/
def BodySimulation {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (cost : Nat → Nat) : Prop :=
  ∀ (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code →
    crepToLoopLocalsRelExact ctxt live source.locals target.locals →
    ∃ extra targetResult targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} = (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧ localsResultRel ctxt live result sourceFinal targetFinal ∧
      extra ≤ cost (CrepSteps.steps p source)

/-- A bounded simulation at one reached source state and an admissible target table. -/
def BodySimulationAt {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source : CrepSemHOLState width σ) (cost : Nat → Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop) : Prop :=
  ∀ (sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code → tableOk target.code →
    crepToLoopLocalsRelExact ctxt live source.locals target.locals →
    ∃ extra targetResult targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} = (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧ localsResultRel ctxt live result sourceFinal targetFinal ∧
      extra ≤ cost (CrepSteps.steps p source)

/-- A universal body simulation applies at any source state and target table. -/
theorem BodySimulation.at {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (cost : Nat → Nat) (source : CrepSemHOLState width σ)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (sim : @BodySimulation width _ σ p ctxt live cost) : BodySimulationAt p ctxt live source cost tableOk := by
  intro final out target run nonerror sr mr gr cr _ lr
  exact sim source final out target run nonerror sr mr gr cr lr

theorem loopFree_bodySimulation {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : LoopFreeCrep p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @BodySimulation width _ σ p ctxt live (fun _ => sizeOf (compileHOLExact ctxt live p)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,post,he,hs,hm,hg,hc,hr,hl,_,bound⟩ :=
    branchProgram_correct_with_bounded_extra p shape source sourceFinal result target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  exact ⟨extra,out,post,he,hs,hm,hg,hc,hr,hl,bound⟩

theorem loopFree_linearBodySimulation {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : LoopFreeCrep p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @BodySimulation width _ σ p ctxt live (fun n => sizeOf (compileHOLExact ctxt live p)*(n+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,post,he,hs,hm,hg,hc,hr,hl,bound⟩ :=
    loopFree_bodySimulation p shape ctxt live source sourceFinal result target
      run nonerror stateRel memRel globalsRel codeRel localsRel
  refine ⟨extra,out,post,he,hs,hm,hg,hc,hr,hl,?_⟩
  nlinarith

end SteppedFlapjack.CrepToLoopSteps
