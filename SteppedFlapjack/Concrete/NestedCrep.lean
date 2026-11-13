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
  concreteDeclCrepState {sourceTemplate with clock := 7}
    (compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))


end SteppedFlapjack.Concrete
