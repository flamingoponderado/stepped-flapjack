import SteppedFlapjack.Concrete.BranchEntryLoop
import SteppedFlapjack.CrepSteps.TailEntryReturn
import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound

/-! Entry-level quantitative simulation for scalar programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- A returning generated tail entry inherits an explicit optimized Loop
clock and visit bound from its Crep entry limit. This specializes the generated
two-program entry layout, where the callee label is 65. -/
theorem generatedScalar_entry_explicit {σ : Type}
    (ctxt : CrepToLoopContextExact) (name : MlString) (p : CrepProgHOL 64)
    (scalar : ScalarProgram p)
    (source entryFinal : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ) (values : List (HolWordLab 64))
    (limit : Nat) (nonzero : source.clock ≠ 0)
    (found : source.code.lookup name = some ([],p))
    (entryRun : evalCrepSemHOLProgExact source (.seq .skip (.call none name [])) =
      (some (.return values),entryFinal))
    (entryBound : CrepSteps.steps (.seq .skip (.call none name [])) source ≤ limit)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt .ln source.locals target.locals)
    (label : findLabExact ctxt name = 65) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let code := compileHOLExact c .ln p
    let budget := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code))*(limit+1)
    ∃ post,
      evaluate branchingLoopEntry {target with clock := target.clock+2*budget} =
        (some (.result (values.map wlabWlocExact)),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*budget} ≤
        loopVisitWeight (optimiseHOL code)*(2*budget+1)+8 ∧
      crepToLoopStateRelExact entryFinal {post with clock := entryFinal.clock} ∧
      crepToLoopMemRelHOLExact entryFinal.memory post.memory entryFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact entryFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt entryFinal.code post.code := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let code := compileHOLExact c .ln p
  let budget := scalarOutputEnvelope (loopVisitWeight (optimiseHOL code))*(limit+1)
  obtain ⟨sourceFinal,calleeRun,calleeBound,finalEq⟩ := CrepSteps.tail_entry_return_inv source entryFinal name p values limit
    found nonzero entryRun entryBound
  have rel := tailCall_nil_entry_relations ctxt .ln source target name p stateRel memRel globalsRel codeRel localsRel found
  obtain ⟨post,run,bound,finalState,finalMem,finalGlobals,finalCode⟩ := scalarProgram_explicit p scalar c .ln
    _ sourceFinal _ _ limit calleeRun calleeBound (.return _)
    rel.1 rel.2.1 rel.2.2.1 rel.2.2.2.1 rel.2.2.2.2
  have targetNonzero : target.clock ≠ 0 := by have h := stateRel.2.2.1; omega
  have clockEq : ({decClock {target with clock := target.clock+2*budget} with locals := .ln} : LoopSemStateFiniteExact 64 σ) =
      {decClock target with locals := .ln, clock := (decClock target).clock+2*budget} := by
    simp only [decClock]
    congr 1
    omega
  have lookup := tailCall_nil_lookup ctxt source {target with clock := target.clock+2*budget} name p codeRel found
  rw [label] at lookup
  have lookup' : findCode (some 65) [] {target with clock := target.clock+2*budget}.code = some (.ln,optimiseHOL code) := by
    simpa [ocompileHOLExact,code,c] using lookup
  have cr : evaluate (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} =
      (some (.result (values.map wlabWlocExact)),post) := by
    rw [clockEq]
    simpa [code,c,resultToLoop] using run
  have cb : LoopSteps.steps (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} ≤
      loopVisitWeight (optimiseHOL code)*(2*budget+1) := by rw [clockEq]; exact bound
  have entry := generatedEntry_return {target with clock := target.clock+2*budget} post (optimiseHOL code) _
    (loopVisitWeight (optimiseHOL code)*(2*budget+1)) (by simp only; omega) lookup' cr cb
  refine ⟨post,entry.1,entry.2,?_,?_,?_,?_⟩
  · rw [finalEq]; simpa [CrepSemHOLState.emptyLocals,crepToLoopStateRelExact] using finalState
  · rw [finalEq]; simpa [CrepSemHOLState.emptyLocals] using finalMem
  · rw [finalEq]; simpa [CrepSemHOLState.emptyLocals] using finalGlobals
  · rw [finalEq]; simpa [CrepSemHOLState.emptyLocals,c,ctxtFcExact,crepToLoopCodeRelExact] using finalCode
end SteppedFlapjack.Concrete
