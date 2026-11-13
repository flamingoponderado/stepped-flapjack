import SteppedFlapjack.Concrete.GlobalStructCrep
import Flapjack.Pancake.CrepInline.InlineRouteBridge
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.CrepInlineRoute
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The renamed global body has no function calls, so renaming fixes it. -/
theorem globalStruct_fperm (a b : MlString) :
    fpermHOL a b (progToHOL globalStructWitness) = progToHOL globalStructWitness := by
  simp [globalStructWitness,progToHOL,expToHOL,fpermHOL]

theorem globalStruct_compiledDecls :
    compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
        (resortDeclsHOL globalStructProgram)) =
      ([.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 0,.const 0])],
       [.function ⟨newMainNameHOL globalStructProgram,false,false,[],
         compileProgExactHOL globalStructContext (progToHOL globalStructWitness),.one⟩],[],globalStructContext) := by
  simp only [globalStructProgram,globalStructDecl,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter_cons,List.filter_nil,if_true,if_false,Bool.false_eq_true,List.nil_append,
    List.cons_append,List.append_nil,fpermDecsHOL]
  simp [compileDecsExactHOL,globalStructStart,globalStructContext,globalStructDecl,
    compileDecsGlobalAddressExact_eq,sizeOfShapeHOL,cakeBytesInWord,compileExpExactHOL,compileExpExactHOLList,
    globalStruct_fperm,fpermName]


theorem globalStruct_compileTop :
    compileTopExactHOL globalStructProgram (ofString "main") =
      [.function ⟨ofString "main",false,false,[],
        .seq (.seq (.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 0,.const 0])) .skip)
          (.call none (newMainNameHOL globalStructProgram) []),.one⟩,
       .function ⟨newMainNameHOL globalStructProgram,false,false,[],
         compileProgExactHOL globalStructContext (progToHOL globalStructWitness),.one⟩] := by
  obtain ⟨inits,funs,exns,ctx,compiled,top⟩ := compileTop_entry_wrapper globalStructProgram (ofString "main") []
    (progToHOL globalStructWitness) .one globalStruct_function_found
  rw [globalStruct_initialContext,globalStruct_compiledDecls] at compiled
  cases compiled
  simpa [nestedSeqHOL] using top


theorem globalStruct_body_context (ctxt : PanToCrepContextExact 64) (vmax : ctxt.vmax = 0) :
    compileProgExactHOLW ctxt (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) := by
  rw [globalStructWitness_lowering]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,
    globalStructCrepContext,mkCtxtExactHOL,vmax]


theorem globalStruct_actualCrep_callee :
    (newMainNameHOL globalStructProgram,[],
      compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) ∈
      compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main")) := by
  have no := compileTop_noInline globalStructProgram (by simp [globalStructProgram,globalStructDecl,inlinableHOL]) (ofString "main")
  simp only [compileProgDeclsHOLW,no,functionsHOL,List.map_nil,compileInlTopHOLExact_nil]
  rw [globalStruct_compileTop]
  simp only [compileToCrepExactHOLW,functionsHOL,List.map_cons,List.map_nil,crepVarsHOL,List.map_nil,
    sizeOfShapeHOL,sizeOfShapesHOL,List.range_zero,List.mem_cons,List.not_mem_nil,or_false]
  right
  simp only [Prod.mk.injEq,true_and]
  unfold compFuncExactHOLW
  symm
  apply globalStruct_body_context
  simp [mkCtxtExactHOL,sizeOfShapeHOL]

theorem globalStruct_fresh : newMainNameHOL globalStructProgram ≠ ofString "main" := by
  intro equal
  have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
    ((functionsHOL globalStructProgram).map Prod.fst)
  apply notMem
  simp [newMainNameHOL,globalStructProgram,globalStructDecl,functionsHOL] at equal ⊢
  exact equal

theorem globalStruct_compiled_names_unique :
    ((compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main"))).map Prod.fst).Nodup := by
  apply panToCrepFirstCompileProgAllDistinctExact
  rw [globalStruct_compileTop]
  simp [functionsHOL,Ne.symm globalStruct_fresh]

theorem globalStruct_actualCrep_lookup :
    (alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main")))).lookup
      (newMainNameHOL globalStructProgram) =
      some ([],compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) := by
  let entries := compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main"))
  have unique : (entries.map Prod.fst).Nodup := globalStruct_compiled_names_unique
  have lookup : List.lookup (newMainNameHOL globalStructProgram) entries = some
      ([],compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) := by
    exact PanGlobalsCompileTopSemanticsDecls.lookupOfMemNodup entries _ _ globalStruct_actualCrep_callee unique
  unfold alistToFmapCodeExact
  rw [PanGlobalsCompileTopSemanticsDecls.emptyUpdateListLookup]
  · simpa [entries,PanGlobalsCompileTopSemanticsDecls.lookupReverseOfNodup _ _ unique] using lookup
  · simpa [entries,List.map_reverse,List.Nodup,List.pairwise_reverse] using unique.imp (fun h => Ne.symm h)


end SteppedFlapjack.Concrete
