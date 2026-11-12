import SteppedFlapjack.Concrete.GlobalStructEntry
import Flapjack.Pancake.CrepInline.InlineRouteBridge
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.CrepInlineRoute
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem globalStruct_actualPrograms_length : globalStructCallPrograms.length = 2 := by
  have no := compileTop_noInline globalStructProgram (by simp [globalStructProgram,globalStructDecl,inlinableHOL]) (ofString "main")
  unfold globalStructCallPrograms
  simp only [compileProgDeclsHOLW,no,functionsHOL,List.map_nil,compileInlTopHOLExact_nil]
  rw [globalStruct_compileTop]
  simp [compileToCrepExactHOLW,functionsHOL]


theorem globalStruct_actualPrograms_eq :
    globalStructCallPrograms =
      [(ofString "main",[],.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])),
       (newMainNameHOL globalStructProgram,[],globalStructActualBody)] := by
  obtain ⟨h,entry⟩ := globalStruct_actualCrep_entry
  have ctxtEq : let lowered := compileTopExactHOL globalStructProgram (ofString "main")
      let ctxt := mkCtxtExactHOL (panToCrepMakeVmapHOLExact []) (makeFuncsExactHOL (functionsHOL lowered))
        (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
      compileProgExactHOLW ctxt (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1) = globalStructActualInit := by
    dsimp only
    apply globalStruct_initializer_context
    simp [mkCtxtExactHOL,sizeOfShapeHOL,sizeOfShapesHOL]
  dsimp only at ctxtEq
  have first : (globalStructCallPrograms[0]'h) =
      (ofString "main",[],.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])) := by
    change (globalStructCallPrograms[0]'h) = _ at entry
    rw [ctxtEq] at entry
    exact entry
  have member : (newMainNameHOL globalStructProgram,[],globalStructActualBody) ∈ globalStructCallPrograms := globalStruct_actualCrep_callee
  have length := globalStruct_actualPrograms_length
  cases ht : globalStructCallPrograms with
  | nil => simp [ht] at length
  | cons a tail =>
    cases tail with
    | nil => simp [ht] at length
    | cons b rest =>
      cases rest with
      | cons c rest => simp [ht] at length
      | nil =>
        simp only [ht,List.getElem_cons_zero] at first
        subst a
        simp only [ht,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with same | same
        · have bad := congrArg Prod.fst same
          exact False.elim (globalStruct_fresh bad)
        · subst b
          rfl


theorem globalStruct_actualBody_branch : SteppedFlapjack.CrepToLoopSteps.BranchProgram globalStructActualBody := by
  unfold globalStructActualBody
  rw [globalStructWitness_lowering]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,cexpHeads,loadShapeBytesHOLW,compFieldHOL]
  simp [List.range_succ,List.range_zero,nestedDecsHOL,crepNestedSeqHOL,storesHOL,Function.comp_def]
  repeat' first | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.seq | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.dec
                | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.expr | apply ExprProgram.store | apply ExprProgram.returnOne
                | apply ExprProgram.leaf | apply DirectExpression.op | apply DirectExpression.load
                | apply DirectExpression.topAddr | apply DirectExpression.const | apply DirectExpression.var | constructor


theorem globalStruct_actualCode_shapes : ∀ name params body,
    (name,params,body) ∈ globalStructCallPrograms → SupportedCodeBody body := by
  intro name params body member
  rw [globalStruct_actualPrograms_eq] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
  · exact .tail (globalStruct_initializer_branch globalStructCrepContext) _
  · exact .branch globalStruct_actualBody_branch


def globalStructActualLoopContext : CrepToLoopContextExact :=
  mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable globalStructCallPrograms) 0

noncomputable def globalStructActualLoopState : LoopSemStateFiniteExact 64 Unit :=
  concreteDeclLoopState riscvConfig.isa globalStructCallCrep globalStructCallPrograms

theorem globalStruct_actualCode_relation : crepToLoopCodeRelExact globalStructActualLoopContext
    globalStructCallCrep.code globalStructActualLoopState.code := by
  apply wholeCrep_supported_executable_codeRel riscvConfig.isa globalStructCallPrograms (ofString "main")
    (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) []))
  · exact globalStruct_compiled_names_unique
  · rw [globalStruct_actualPrograms_eq]
    simp [holAlookup]
  · exact globalStruct_actualCode_shapes


def globalStructActualPanProgram : ProgHOL 64 := .seq
  (nestedSeqHOL (compileDecsExactHOL globalStructStart
    (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)
  (.call none (newMainNameHOL globalStructProgram) [])

theorem globalStruct_actualPan_shape : CallFrontend globalStructCrepContext globalStructActualPanProgram :=
  .seq (.base (globalStruct_initializer_frontend globalStructStart)) (.tail (by simp))

theorem globalStruct_actualPan_compiled : compileProgExactHOLW globalStructCrepContext globalStructActualPanProgram =
    .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) []) := by
  simp [globalStructActualPanProgram,globalStructActualInit,compileProgExactHOLW,compileCallNoReturnExactHOLW,
    compileExpExactHOLWList]

theorem globalStruct_actualCode_sources : ∀ row ∈ globalStructCallPrograms,
    ∃ (ctx : PanToCrepContextExact 64) (p : ProgHOL 64),
      row.2.2 = compileProgExactHOLW ctx p ∧ CallFrontend ctx p := by
  intro row member
  rw [globalStruct_actualPrograms_eq] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact ⟨globalStructCrepContext,globalStructActualPanProgram,globalStruct_actualPan_compiled.symm,globalStruct_actualPan_shape⟩
  · exact ⟨globalStructCrepContext,compileProgExactHOL globalStructContext (progToHOL globalStructWitness),rfl,.base globalStruct_frontend⟩

def globalStructActualLoopClock : Nat :=
  callClockFactor globalStructActualLoopContext (globalStructCallPrograms.map (fun row => (row.2.1,row.2.2)))
    globalStructCallCrep.clock (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])) * (globalStructActualEntryLimit+1)

def globalStructActualLoopLimit : Nat :=
  callSyntaxCost globalStructActualLoopContext (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])) +
    max (callSyntaxCost globalStructActualLoopContext (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])))
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms))+2) * (globalStructCallCrep.clock+globalStructActualLoopClock)

/-- The actual entry and function table execute in Loop at a code-derived clock. -/
theorem globalStruct_actualLoop_run : ∃ crepPost loopPost,
    evalCrepSemHOLProgExact globalStructCallCrep (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])) =
      (some (.return [.word 8]),crepPost) ∧
    LoopSemStateFiniteExact.evaluate
      (compileHOLExact globalStructActualLoopContext .ln (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])))
      {globalStructActualLoopState with clock := globalStructActualLoopState.clock+globalStructActualLoopClock} =
        (some (.result [.word 8]),loopPost) ∧
    SteppedFlapjack.LoopSteps.steps
      (compileHOLExact globalStructActualLoopContext .ln (.seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])))
      {globalStructActualLoopState with clock := globalStructActualLoopState.clock+globalStructActualLoopClock} ≤ globalStructActualLoopLimit := by
  obtain ⟨h,crepPost,run,bound⟩ := globalStruct_actualEntry_run
  simp only [globalStruct_actualPrograms_eq,List.getElem_cons_zero] at run bound
  have relations := concreteDecl_crepLoop_relations riscvConfig.isa globalStructCallCrep globalStructCallPrograms rfl
  have locals : crepToLoopLocalsRelExact globalStructActualLoopContext .ln globalStructCallCrep.locals globalStructActualLoopState.locals := by
    apply empty_crepLoop_locals
    rfl
  have table := callFrontend_compiled_loopTableSupported riscvConfig.isa globalStructCallPrograms globalStruct_actualCode_sources
  obtain ⟨post,ev,visits,_,_,_,_,_⟩ := callFrontend_wholeVisits_explicit globalStructCrepContext globalStructActualPanProgram
    globalStruct_actualPan_shape globalStructCallPrograms globalStruct_actualCode_sources globalStructActualLoopContext globalStructActualLoopContext .ln
    globalStructCallCrep crepPost (some (.return [.word 8])) globalStructActualLoopState rfl
    (by simpa [globalStruct_actualPan_compiled] using run) (by simp) (by simp) globalStructActualEntryLimit (by simpa [globalStruct_actualPan_compiled] using bound)
    relations.1 relations.2.1 relations.2.2 globalStruct_actualCode_relation table locals
  refine ⟨crepPost,post,run,?_,?_⟩
  · simpa [globalStruct_actualPan_compiled,globalStructActualLoopClock,resultToLoop,wlabWlocExact] using ev
  · have code : globalStructActualLoopState.code = sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms) := rfl
    rw [code] at visits
    simp only [code]
    simpa [globalStruct_actualPan_compiled,globalStructActualLoopClock,globalStructActualLoopLimit] using visits

end SteppedFlapjack.Concrete
