import SteppedFlapjack.Concrete.NestedCalls
import SteppedFlapjack.Concrete.CrepCode
/-! Concrete compiler output for the nested-call witness. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps
set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Global lowering retains all source functions, with a fresh entry name. -/
theorem nestedCall_lowered_declarations : compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main") =
  [.function ⟨ofString "main",false,false,[],.seq .skip (.call none (ofString "main'") []),.one⟩,
   .function ⟨ofString "main'",false,true,[],.decCall (ofString "answer") .one (ofString "middle") [] (.return (.var .local (ofString "answer"))),.one⟩,
   .function ⟨ofString "middle",false,false,[],.call none (ofString "leaf") [],.one⟩,
   .function ⟨ofString "leaf",false,false,[],.return (.const 7),.one⟩] := by
  simp [compileTopExactHOL,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,
    progToHOL,expToHOL,shapeToHOL,functionsHOL,compileTopFunctionLookup_eq_lookup,List.lookup,
    resortDeclsHOL,newMainNameHOL,isNameHOL,isDeclHOL,isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,
    MlString.explode_implode]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,
    compileExpExactHOL,compileExpExactHOLList,ofString]
set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The original frontend produces four functions, preserving ordinary and tail calls. -/
theorem nestedCall_crep_code : compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")) =
  [(ofString "main", [], .seq .skip (.call none (ofString "main'") [])),
   (ofString "main'", [], .dec 1 (.const 0) (.seq (.call (some ([1],none)) (ofString "middle") []) (.return [.var 1]))),
   (ofString "middle", [], .call none (ofString "leaf") []),
   (ofString "leaf", [], .return [.const 7])] := by
  rw [nestedCall_lowered_declarations]
  simp [compileProgDeclsHOLW,inlinableHOL,functionsHOL,CrepInlineRoute.compileInlTopHOLExact_nil,
    compileToCrepExactHOLW,compFuncExactHOLW,crepVarsHOL,compileProgExactHOLW,
    compileCallNoReturnExactHOLW,compileExpExactHOLWList,compileDecCallExactHOLW,
    compileReturnExactHOLW,compileExpExactHOLW,panToCrepMakeVmapHOLExact,mkCtxtExactHOL,
    FUPDATE,sizeOfShapeHOL,makeFuncsExactHOL,HolFiniteMapExact.lookup_update,nestedDecsHOL]

/-- The generated Crep code installed over the source fixture memory. -/
def nestedCrepState : CrepSemHOLState 64 Unit :=
  concreteDeclCrepState {sourceTemplate with clock := 4}
    (compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))

set_option maxHeartbeats 3000000 in
/-- The actual generated entry executes both calls and returns seven. -/
theorem nestedCall_crep_run :
    ∃ final, evalCrepSemHOLProgExact nestedCrepState
      (.seq .skip (.call none (ofString "main'") [])) =
      (some (.return [.word 7]),final) ∧ final.ffi = sourceFfi := by
  have a : ofString "main" ≠ ofString "main'" := by decide
  have b : ofString "main" ≠ ofString "middle" := by decide
  have c : ofString "main'" ≠ ofString "middle" := by decide
  have d : ofString "main" ≠ ofString "leaf" := by decide
  have e : ofString "main'" ≠ ofString "leaf" := by decide
  have f : ofString "middle" ≠ ofString "leaf" := by decide
  simp [a,b,c,d,e,f,nestedCrepState,nestedCall_crep_code,concreteDeclCrepState,alistToFmapCodeExact,
    evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip,
    evalCrepSemHOLProgExact_call_holShape,evalCrepSemHOLProgExact_dec_holShape,
    evalCrepSemHOLProgExact_return_holShape,lookupCodeFiniteHOL,evalCrepSemHOLExp,
    sourceTemplate,HolFiniteMapExact.lookup_updateList,FUPDATE,FUPDATE_LIST,crepReturnInfoNodupError,decClockCrepSemHOL,
    FUPDATE_HOL,FUPDATE_LIST_HOL,HolFiniteMapExact.lookup_updateEq,HolFiniteMapExact.lookup_updateListEq,
    CrepSemHOLState.emptyLocals]

set_option maxHeartbeats 3000000 in
/-- The generated entry and reached callees execute nine Crep statements. -/
theorem nestedCall_crep_steps :
    SteppedFlapjack.CrepSteps.steps (.seq .skip (.call none (ofString "main'") [])) nestedCrepState = 9 := by
  have a : ofString "main" ≠ ofString "main'" := by decide
  have b : ofString "main" ≠ ofString "middle" := by decide
  have c : ofString "main'" ≠ ofString "middle" := by decide
  have d : ofString "main" ≠ ofString "leaf" := by decide
  have e : ofString "main'" ≠ ofString "leaf" := by decide
  have f : ofString "middle" ≠ ofString "leaf" := by decide
  simp [SteppedFlapjack.CrepSteps.steps.eq_def,a,b,c,d,e,f,nestedCrepState,nestedCall_crep_code,
    concreteDeclCrepState,alistToFmapCodeExact,evalCrepSemHOLProgExact_seq_holShape,
    evalCrepSemHOLProgExact_skip,evalCrepSemHOLProgExact_call_holShape,evalCrepSemHOLProgExact_dec_holShape,
    evalCrepSemHOLProgExact_return_holShape,lookupCodeFiniteHOL,evalCrepSemHOLExp,sourceTemplate,
    HolFiniteMapExact.lookup_updateList,FUPDATE,FUPDATE_LIST,crepReturnInfoNodupError,decClockCrepSemHOL,
    FUPDATE_HOL,FUPDATE_LIST_HOL,HolFiniteMapExact.lookup_updateEq,HolFiniteMapExact.lookup_updateListEq,
    CrepSemHOLState.emptyLocals,CrepSemHOLState.setVar]
  have size1 : 1 < 2 + (2 + sizeOf (ofString "main'") + 1) := by omega
  have size2 : 7 + sizeOf (ofString "middle") < 1 + (7 + sizeOf (ofString "middle") + 1) + 4 := by omega
  simp [Prod.lex_def,size1,size2]


end SteppedFlapjack.Concrete
