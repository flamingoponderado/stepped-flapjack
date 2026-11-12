import SteppedFlapjack.Concrete.GlobalStructWitness
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.CrepSteps.BranchStatic
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

def globalStructCrepContext : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty

def globalStructCrepState : CrepSemHOLState 64 Unit := concreteDeclCrepState globalStructTarget []


theorem globalStruct_crep_static : SteppedFlapjack.CrepSteps.StaticProgram
    (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) := by
  rw [globalStructWitness_lowering]
  simp only [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,
    nestedDecsHOL]
  repeat' first | apply SteppedFlapjack.CrepSteps.StaticProgram.seq
                | apply SteppedFlapjack.CrepSteps.StaticProgram.dec
                | exact SteppedFlapjack.CrepSteps.StaticProgram.leaf _ rfl

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
