import SteppedFlapjack.Concrete.GlobalStructWitness
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.CrepSteps.BranchStatic
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
import SteppedFlapjack.PanToCrepSteps.GlobalInitializers
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

def globalStructCrepContext : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty

/-- The pair's lowered second-field read belongs to the general frontend
fragment, and its compiled expression has the supported Crep-to-Loop shape. -/
theorem globalStruct_field_frontend :
    FrontendScalar globalStructCrepContext
      (.rfield 1 (.load (.comb [.one,.one]) (.op .sub [.topAddr,.const 16]))) := by
  exact .fieldLoad 1 2 (by decide) (.op .sub .topAddr (.const 16))

theorem globalStruct_field_compiled : ∃ (expression : CrepExpHOL 64),
    compileExpExactHOLW globalStructCrepContext
      (.rfield 1 (.load (.comb [.one,.one]) (.op .sub [.topAddr,.const 16]))) =
        ([expression],.one) ∧ SteppedFlapjack.CrepToLoopSteps.CompiledScalar expression :=
  SteppedFlapjack.CrepToLoopSteps.frontendScalar_compiled globalStruct_field_frontend

/-- Global lowering produces a program in the shared structured-store and
field-load frontend fragment. -/
theorem globalStruct_frontend : FrontendProgram globalStructCrepContext
    (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) := by
  rw [globalStructWitness_lowering]
  apply FrontendProgram.seq
  · apply FrontendProgram.storeStruct (.op .sub .topAddr (.const 16))
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .const _
  · exact .ret globalStruct_field_frontend

/-- Initializers of the declared pair use the general structured frontend for
any starting global layout. -/
theorem globalStruct_initializer_frontend (globals : PanGlobalsContextExact 64) :
    FrontendProgram globalStructCrepContext
      (nestedSeqHOL (compileDecsExactHOL globals globalStructProgram).1) := by
  apply globalCompile_frontend_initializer_sequence
  intro shape name value member
  simp only [globalStructProgram,globalStructDecl,List.mem_cons,List.not_mem_nil,or_false,
    DeclHOL.decl.injEq] at member
  rcases member with ⟨rfl,rfl,rfl⟩ | impossible
  · apply FrontendInitializer.flatStruct
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .const _
  · cases impossible

/-- The compiled declaration initializer has a code-derived visit bound and
satisfies the Crep-to-Loop shape invariant. -/
theorem globalStruct_initializer_compiled (globals : PanGlobalsContextExact 64)
    (state : CrepSemHOLState 64 Unit) :
    let program := compileProgExactHOLW globalStructCrepContext
      (nestedSeqHOL (compileDecsExactHOL globals globalStructProgram).1)
    SteppedFlapjack.CrepToLoopSteps.ScalarProgram program ∧
      SteppedFlapjack.CrepSteps.steps program state ≤ SteppedFlapjack.CrepSteps.statementWeight program := by
  have h := globalStruct_initializer_frontend globals
  exact ⟨SteppedFlapjack.CrepToLoopSteps.frontend_scalar_program h,
    SteppedFlapjack.CrepSteps.staticProgram_statementWeight
      (frontendLoopFree_static h (globalCompile_initializers_noWhile globalStructProgram globals)) state⟩

def globalStructCrepState : CrepSemHOLState 64 Unit := concreteDeclCrepState globalStructTarget []


theorem globalStruct_crep_static : SteppedFlapjack.CrepSteps.StaticProgram
    (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) := by
  apply frontendLoopFree_static globalStruct_frontend
  rw [globalStructWitness_lowering]
  rfl

theorem globalStruct_crep_visits : SteppedFlapjack.CrepSteps.steps
    (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) globalStructCrepState ≤ 10 := by
  have weight : SteppedFlapjack.CrepSteps.statementWeight
      (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) = 10 := by
    rw [globalStructWitness_lowering]
    with_unfolding_all decide
  simpa [weight] using SteppedFlapjack.CrepSteps.staticProgram_statementWeight globalStruct_crep_static globalStructCrepState
/-- The concrete pair program reaches Crep with a ten-visit bound. -/
theorem globalStruct_crep_run : ∃ sourcePost targetPost crepPost,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    evalCrepSemHOLProgExact globalStructCrepState
      (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) =
        (some (.return [.word 8]),crepPost) ∧ panToCrepStateRelFiniteExact targetPost crepPost ∧
      SteppedFlapjack.CrepSteps.steps
        (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) globalStructCrepState ≤ 10 := by
  obtain ⟨sourcePost,targetPost,sourceRun,targetRun,_⟩ := globalStruct_lowered_run
  have stateRel : panToCrepStateRelFiniteExact globalStructTarget globalStructCrepState := by
    exact concreteDecl_panCrep_stateRel globalStructTarget [] rfl rfl
  have codeRel : codeRelExactHOLW globalStructCrepContext globalStructTarget.code globalStructCrepState.code := by
    simp [codeRelExactHOLW,globalStructTarget,sourceTemplate,HolFiniteMapExact.lookup_empty]
  have excpRel : panToCrepExcpRelFiniteExact globalStructCrepContext.eids globalStructTarget.eshapes := by
    simpa [globalStructCrepContext,mkCtxtExactHOL,globalStructTarget,sourceTemplate] using (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact globalStructCrepContext globalStructTarget.locals globalStructCrepState.locals := by
    apply empty_panCrep_locals
    rfl
  have localised : localisedProgHOL (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) = true := by
    rw [globalStructWitness_lowering]
    simp [localisedProgHOL,localisedExpHOL,everyExpHOL,everyExpListHOL]
  obtain ⟨result,crepPost,crepRun,postState,_,_,resultRel⟩ := pcCompileCorrect
    (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) globalStructTarget
    (some (.returned (.val (.word (8 : BitVec 64))))) targetPost globalStructCrepState globalStructCrepContext
    ⟨targetRun,by simp,stateRel,codeRel,excpRel,localsRel,localised⟩
  have resultEq : result = some (.return [.word 8]) := by simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst result
  refine ⟨sourcePost,targetPost,crepPost,sourceRun,targetRun,?_,postState,globalStruct_crep_visits⟩
  simpa [flattenHOL] using crepRun

end SteppedFlapjack.Concrete
