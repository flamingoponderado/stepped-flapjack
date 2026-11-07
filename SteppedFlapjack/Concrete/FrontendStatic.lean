import SteppedFlapjack.Concrete.FrontendShape
import SteppedFlapjack.CrepSteps.BranchStatic
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! Loop-free frontend programs compile to statically bounded Crep programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepSteps

/-- The concrete comparison witness instantiates the generalized static bound. -/
theorem branching_compiled_visits (ctxt : PanToCrepContextExact 64) {σ : Type}
    (state : CrepSemHOLState 64 σ) :
    steps (compileProgExactHOLW ctxt branchingHOL) state ≤
      sizeOf (compileProgExactHOLW ctxt branchingHOL) := by
  apply staticProgram_steps
  apply frontendLoopFree_static (branching_frontend_shape ctxt)
  simp [noWhile,branchingHOL]

/-- A concrete false comparison loop witnesses the generalized while bound. -/
def falseComparisonLoop : ProgHOL 64 :=
  .while (.cmp .lower (.const 1) (.const 0)) .skip

def emptyFrontendContext : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty

def emptyFrontendCrep : CrepSemHOLState 64 Unit := concreteDeclCrepState sourceTemplate []

/-- The comparison-capable while theorem applies to concrete related states. -/
theorem falseComparisonLoop_crep_bound :
    steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤ 2 ∧
    ∃ targetResult targetFinal,
      evalCrepSemHOLProgExact emptyFrontendCrep (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) =
        (targetResult,targetFinal) ∧
      pcCompileCorrectResultRel emptyFrontendContext sourceTemplate targetFinal none targetResult ∧
      steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤
        sizeOf (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) := by
  have condition : FrontendScalar emptyFrontendContext (.cmp .lower (.const 1) (.const 0)) :=
    .cmp .lower (.const 1) (.const 0)
  have body : StaticProgram (compileProgExactHOLW emptyFrontendContext (.skip : ProgHOL 64)) := by
    simpa [compileProgExactHOLW] using (StaticProgram.leaf (.skip : CrepProgHOL 64) rfl)
  have run : sourceTemplate.evaluateHOLFiniteState falseComparisonLoop = (none,sourceTemplate) := by
    rw [falseComparisonLoop,PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have stateRel : panToCrepStateRelFiniteExact sourceTemplate emptyFrontendCrep :=
    concreteDecl_panCrep_stateRel sourceTemplate [] rfl rfl
  have codeRel : codeRelExactHOLW emptyFrontendContext sourceTemplate.code emptyFrontendCrep.code := by
    intro function args program ret found
    simp [sourceTemplate,HolFiniteMapExact.lookup_empty] at found
  have excpRel : panToCrepExcpRelFiniteExact emptyFrontendContext.eids sourceTemplate.eshapes := by
    simpa [emptyFrontendContext,sourceTemplate,mkCtxtExactHOL] using (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact emptyFrontendContext sourceTemplate.locals emptyFrontendCrep.locals := by
    apply empty_panCrep_locals
    rfl
  have bound := while_compiled_steps_general (.cmp .lower (.const 1) (.const 0)) .skip
    emptyFrontendContext condition body sourceTemplate sourceTemplate none emptyFrontendCrep
    run (by simp) stateRel codeRel excpRel localsRel (by simp [localisedProgHOL,localisedExpHOL,everyExpHOL])
  have count : controlSteps falseComparisonLoop sourceTemplate = 1 := by
    rw [falseComparisonLoop,controlSteps_while]
    simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  change steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤
    (1 + sizeOf (compileProgExactHOLW emptyFrontendContext (.skip : ProgHOL 64))) *
      controlSteps falseComparisonLoop sourceTemplate at bound
  rw [count] at bound
  have directBound : steps (compileProgExactHOLW emptyFrontendContext falseComparisonLoop) emptyFrontendCrep ≤ 2 := by
    simpa [compileProgExactHOLW] using bound
  have shape : FrontendProgram emptyFrontendContext falseComparisonLoop := .while condition .skip
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,spanBound⟩ :=
    frontend_correct_with_steps emptyFrontendContext falseComparisonLoop shape sourceTemplate sourceTemplate none
      emptyFrontendCrep 1 run (by simp) (by omega) stateRel codeRel excpRel localsRel
  refine ⟨directBound,targetResult,targetFinal,targetRun,resultRel,?_⟩
  simpa using spanBound

end SteppedFlapjack.Concrete
