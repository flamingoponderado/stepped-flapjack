import SteppedFlapjack.Concrete.NestedCrep
import SteppedFlapjack.Concrete.NestedSourceHOL
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
/-! The multi-function witness instantiates the whole-program Crep/Loop code relation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps

def nestedCallCrepPrograms : List (MlString × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))

/-- The generated four-function Crep table has maximum statement weight four. -/
theorem nestedCall_crep_codeWeight : SteppedFlapjack.CrepSteps.codeWeight nestedCallCrepPrograms = 4 := by
  rw [nestedCallCrepPrograms,nestedCall_crep_code]
  rfl

/-- The generated Loop table has the compiler code relation for every Crep function. -/
theorem nestedCall_loop_code_relation : crepToLoopCodeRelExact
      (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable nestedCallCrepPrograms) 0)
      (alistToFmapCodeExact nestedCallCrepPrograms) (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)) := by
  apply callFrontend_declaration_crepLoop_codeRel _ _ nestedCall_inline_selection_empty nestedCall_declaration_shapes
    (ofString "main") (.seq .skip (.call none (ofString "main'") []))
  · rw [nestedCall_lowered_declarations]; decide
  · rw [nestedCall_crep_code]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The lowered source and generated Crep tables satisfy the compiler code relation. -/
theorem nestedCall_panCrep_code_relation : codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL
        (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
      (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse)
      (alistToFmapCodeExact nestedCallCrepPrograms) := by
  apply callFrontend_declaration_codeRel
  · rw [nestedCall_lowered_declarations]
    decide
  · exact nestedCall_inline_selection_empty
  · exact nestedCall_declaration_shapes

/-- The source configuration immediately before the generated entry call. -/
def nestedLoweredSource : PanSemStateFiniteExact 64 Unit :=
  noGlobalsLoweredPreCall {sourceTemplate with clock := 3}
    (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse)

/-- The lowered wrapper follows the same two nested calls and returns seven. -/
theorem nestedLoweredSource_run : ∃ final,
    nestedLoweredSource.evaluateHOLFiniteState (.seq .skip (.call none (ofString "main'") [])) =
      (some (.returned (.val (.word 7))),final) ∧ final.ffi = sourceFfi := by
  have a : (ofString "main" == ofString "main'") = false := by decide
  have b : (ofString "main" == ofString "middle") = false := by decide
  have c : (ofString "main'" == ofString "middle") = false := by decide
  have d : (ofString "main" == ofString "leaf") = false := by decide
  have e : (ofString "main'" == ofString "leaf") = false := by decide
  have f : (ofString "middle" == ofString "leaf") = false := by decide
  simp [a,b,c,d,e,f,nestedLoweredSource,noGlobalsLoweredPreCall,nestedCall_lowered_declarations,
    functionsHOL,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_call,
    evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_return,evalListHOLFinite,evalListHOLExact,
    PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,
    HolFiniteMapExact.lookup_update,FUPDATE,callEntryStateHOLFinite,evalHOLExact,
    shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite,sourceTemplate]

/-- The lowered entry's control visits are bounded across both calls. -/
theorem nestedLoweredSource_steps :
    controlSteps (.seq .skip (.call none (ofString "main'") [])) nestedLoweredSource ≤ 7 := by
  have a : (ofString "main" == ofString "main'") = false := by decide
  have b : (ofString "main" == ofString "middle") = false := by decide
  have c : (ofString "main'" == ofString "middle") = false := by decide
  have d : (ofString "main" == ofString "leaf") = false := by decide
  have e : (ofString "main'" == ofString "leaf") = false := by decide
  have f : (ofString "middle" == ofString "leaf") = false := by decide
  simp [controlSteps.eq_def,a,b,c,d,e,f,nestedLoweredSource,noGlobalsLoweredPreCall,nestedCall_lowered_declarations,
    functionsHOL,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_call,evaluateHOLFiniteState_return,
    evalListHOLFinite,evalListHOLExact,PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,callEntryStateHOLFinite,evalHOLExact,
    shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite,sourceTemplate]
  simp only [fixClockHOLFinite,Prod.lex_def]
  split_ifs <;> norm_num at *

/-- The generated wrapper adds at most two visits to the original source entry. -/
theorem nestedLoweredSource_fromOriginal :
    controlSteps (.seq .skip (.call none (ofString "main'") [])) nestedLoweredSource ≤
      2 + controlSteps (.call none (ofString "main") []) {nestedSourceState 1 with clock := 4} := by
  rw [nestedCall_controlSteps]
  exact nestedLoweredSource_steps

/-- The general source-to-Crep bound applies to the actual nested-call entry. -/
theorem nestedCall_sourceToCrep_bound : ∃ final,
    evalCrepSemHOLProgExact nestedCrepState (.seq .skip (.call none (ofString "main'") [])) =
      (some (.return [.word 7]),final) ∧ final.ffi = sourceFfi ∧
    SteppedFlapjack.CrepSteps.steps (.seq .skip (.call none (ofString "main'") [])) nestedCrepState ≤
      4 * (2 + controlSteps (.call none (ofString "main") []) {nestedSourceState 1 with clock := 4}) := by
  let decls := compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")
  let ctxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL decls)) 0
    (getEidsFromDeclsHOL decls)
  let entry : ProgHOL 64 := .seq .skip (.call none (ofString "main'") [])
  have unique : ((functionsHOL decls).map Prod.fst).Nodup := by
    dsimp [decls]
    rw [nestedCall_lowered_declarations]
    decide
  have noEx : getEidsFromDeclsHOL decls = HolFiniteMapExact.empty := by
    dsimp [decls]
    rw [nestedCall_lowered_declarations]
    rfl
  have shape : CallFrontend ctxt entry := .seq (.base .skip) (.tail (by simp))
  obtain ⟨sourceFinal,sourceRun,sourceFfiEq⟩ := nestedLoweredSource_run
  have span := callFrontend_declaration_steps decls unique nestedCall_inline_selection_empty
    nestedCall_declaration_shapes entry shape nestedLoweredSource sourceFinal
    (some (.returned (.val (.word 7)))) rfl rfl rfl rfl rfl noEx sourceRun (by simp)
    (2 + controlSteps (.call none (ofString "main") []) {nestedSourceState 1 with clock := 4}) nestedLoweredSource_fromOriginal
  obtain ⟨targetResult,targetFinal,targetRun,finalState,_,_,resultRel,bound⟩ := span
  have compiled : compileProgExactHOLW ctxt entry = .seq .skip (.call none (ofString "main'") []) := by
    simp [ctxt,entry,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  have start : concreteDeclCrepState nestedLoweredSource (compileProgDeclsHOLW decls) = nestedCrepState := by
    rfl
  have tableWeight : CrepSteps.codeWeight (compileProgDeclsHOLW decls) = 4 := nestedCall_crep_codeWeight
  have resultEq : targetResult = some (.return [.word 7]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  rcases finalState with ⟨_,_,_,_,_,_,_,finalFfi,_,_⟩
  rw [compiled,start] at targetRun
  rw [resultEq] at targetRun
  rw [compiled,start,tableWeight] at bound
  simp only [CrepSteps.statementWeight] at bound
  norm_num at bound
  exact ⟨targetFinal,targetRun,finalFfi.symm.trans sourceFfiEq,bound⟩

/-- The shared structural optimizer computes the original Loop compiler output
for every function of the nested-call witness. -/
theorem nestedCall_structuralLive_eq :
    compileProgWithStructuralLive riscvConfig.isa nestedCallCrepPrograms =
      compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms := by
  rw [nestedCallCrepPrograms,compileProgDeclsHOLW,nestedCall_inline_selection_empty,
    CrepInlineRoute.compileInlTopHOLExact_nil]
  exact callFrontend_compileProgWithStructuralLive_eq _ _
    (callFrontend_declaration_sources _ nestedCall_declaration_shapes)

def nestedLoopLive1 : NumSet := sptInsert 1 () .ln

def nestedLoopCode64 : HolLoopProg 64 :=
 .mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))

def nestedLoopCode65 : HolLoopProg 64 :=
 .mark <| .seq (.mark .skip) <| .mark <| .seq (.mark .skip) <| .mark <| .seq
   (.mark <| .seq (.mark <| .call (some ([1],.ln)) (some 66) [] (some (2,.mark (.raise 2),.mark .skip,nestedLoopLive1))) (.mark .skip))
   (.mark <| .seq (.mark (.assign 2 (.var 1))) (.mark <| .seq (.mark (.return [2])) (.mark .skip)))

def nestedLoopCode66 : HolLoopProg 64 :=
 .mark (.seq (.mark (.call none (some 67) [] none)) (.mark .skip))

def nestedLoopCode67 : HolLoopProg 64 :=
 .mark (.seq (.mark (.assign 1 (.const 7))) (.mark (.seq (.mark (.return [1])) (.mark .skip))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The real Loop compiler produces the four concrete optimized functions. -/
theorem nestedCall_loop_code : compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms =
 [(64,[],nestedLoopCode64),(65,[],nestedLoopCode65),(66,[],nestedLoopCode66),(67,[],nestedLoopCode67)] := by
  rw [← nestedCall_structuralLive_eq]
  rw [nestedCallCrepPrograms,nestedCall_crep_code]
  with_unfolding_all rfl

end SteppedFlapjack.Concrete
