import SteppedFlapjack.Concrete.GlobalStructCallee
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem globalStruct_initializer_context (ctxt : PanToCrepContextExact 64) (vmax : ctxt.vmax = 0) :
    compileProgExactHOLW ctxt (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1) =
    compileProgExactHOLW globalStructCrepContext (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1) := by
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,
    globalStructCrepContext,mkCtxtExactHOL,vmax]

def globalStructCallPrograms := compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main"))
def globalStructCallPan := {globalStructTarget with clock := 1}
def globalStructCallCrep := concreteDeclCrepState globalStructCallPan globalStructCallPrograms

theorem globalStruct_crep_initializer_run : ∃ post,
    evalCrepSemHOLProgExact globalStructCallCrep
      (compileProgExactHOLW globalStructCrepContext (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)) = (none,post) ∧
    panToCrepStateRelFiniteExact globalStructCallPan post ∧
    post.code = globalStructCallCrep.code := by
  let init := nestedSeqHOL (compileDecsExactHOL globalStructStart
    (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1
  have run : globalStructCallPan.evaluateHOLFiniteState init = (none,globalStructCallPan) := by
    simpa [globalStructCallPan,init] using globalStruct_initializer_run_clock 1
  have sr : panToCrepStateRelFiniteExact globalStructCallPan globalStructCallCrep := by
    exact concreteDecl_panCrep_stateRel globalStructCallPan globalStructCallPrograms rfl rfl
  have cr : codeRelExactHOLW globalStructCrepContext globalStructCallPan.code globalStructCallCrep.code := by
    simp [codeRelExactHOLW,globalStructCallPan,globalStructTarget,sourceTemplate,HolFiniteMapExact.lookup_empty]
  have er : panToCrepExcpRelFiniteExact globalStructCrepContext.eids globalStructCallPan.eshapes := by
    simpa [globalStructCrepContext,mkCtxtExactHOL,globalStructCallPan,globalStructTarget,sourceTemplate] using (empty_panCrep_exceptions (width := 64))
  have lr : panToCrepLocalsRelFiniteExact globalStructCrepContext globalStructCallPan.locals globalStructCallCrep.locals := by
    apply empty_panCrep_locals
    rfl
  obtain ⟨res,post,crepRun,postRel,_,_,resultRel⟩ := pcCompileCorrect init globalStructCallPan none globalStructCallPan
    globalStructCallCrep globalStructCrepContext ⟨run,by simp,sr,cr,er,lr,
      frontendProgram_localised (globalStruct_initializer_frontend globalStructStart)⟩
  have eq : res = none := resultRel.1
  subst res
  exact ⟨post,crepRun,postRel,evaluateCodeInvariantHOL _ _ _ _ crepRun⟩


theorem globalStruct_crep_callee_run (post : CrepSemHOLState 64 Unit)
    (relation : panToCrepStateRelFiniteExact globalStructCallPan post) :
    ∃ final, evalCrepSemHOLProgExact (decClockCrepSemHOL {post with locals := HolFiniteMapExact.empty})
      (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) =
        (some (.return [.word 8]),final) ∧ final.ffi = sourceFfi := by
  obtain ⟨sourcePost,sourceRun,sourceFfiEq⟩ := globalStruct_source_run_clock 0
  let called := decClockCrepSemHOL {post with locals := HolFiniteMapExact.empty}
  have sr : panToCrepStateRelFiniteExact {globalStructTarget with clock := 0} called := by
    rcases relation with ⟨mem,dom,sh,structs,globals,clk,be,ffi,base,top⟩
    simp only [panToCrepStateRelFiniteExact,called,decClockCrepSemHOL]
    simp only [globalStructCallPan] at *
    refine ⟨mem,dom,sh,structs,globals,?_,be,ffi,base,top⟩
    omega
  have cr : codeRelExactHOLW globalStructCrepContext ({globalStructTarget with clock := 0}).code called.code := by
    simp [codeRelExactHOLW,globalStructTarget,sourceTemplate,HolFiniteMapExact.lookup_empty]
  have er : panToCrepExcpRelFiniteExact globalStructCrepContext.eids ({globalStructTarget with clock := 0}).eshapes := by
    simpa [globalStructCrepContext,mkCtxtExactHOL,globalStructTarget,sourceTemplate] using (empty_panCrep_exceptions (width := 64))
  have lr : panToCrepLocalsRelFiniteExact globalStructCrepContext ({globalStructTarget with clock := 0}).locals called.locals := by
    apply empty_panCrep_locals
    rfl
  obtain ⟨targetPost,res,final,targetRun,globalFinal,crepRun,postRel,resultRel,_⟩ :=
    globalFrontend_correct_with_steps globalStructContext globalStructCrepContext (progToHOL globalStructWitness)
      globalStruct_sourceFrontend {globalStructHOL with clock := 0} sourcePost {globalStructTarget with clock := 0}
      (some (.returned (.val (.word (8 : BitVec 64))))) called 3 sourceRun (by simp) (globalStruct_source_visits 0)
      (globalStruct_stateRel_clock 0) sr cr er lr
  have eq : res = some (.return [.word 8]) := by simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst res
  rcases globalFinal with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,sourceTargetFfi,_⟩
  rcases postRel with ⟨_,_,_,_,_,_,_,targetCrepFfi,_,_⟩
  exact ⟨final,by simpa [called,flattenHOL] using crepRun,
    targetCrepFfi.symm.trans (sourceTargetFfi.symm.trans sourceFfiEq)⟩


theorem globalStruct_actualTail_run : ∃ post final,
    evalCrepSemHOLProgExact globalStructCallCrep
      (compileProgExactHOLW globalStructCrepContext (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)) = (none,post) ∧
    evalCrepSemHOLProgExact post (.call none (newMainNameHOL globalStructProgram) []) =
      (some (.return [.word 8]),final) ∧
    panToCrepStateRelFiniteExact globalStructCallPan post ∧ post.code = globalStructCallCrep.code ∧ final.ffi = sourceFfi := by
  obtain ⟨post,initRun,relation,codeEq⟩ := globalStruct_crep_initializer_run
  obtain ⟨final,bodyRun,finalFfi⟩ := globalStruct_crep_callee_run post relation
  have found : post.code.lookup (newMainNameHOL globalStructProgram) = some
      ([],compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) := by
    rw [codeEq]
    exact globalStruct_actualCrep_lookup
  have clock : post.clock ≠ 0 := by
    have h := relation.2.2.2.2.2.1
    simp [globalStructCallPan] at h
    omega
  refine ⟨post,CrepSemHOLState.emptyLocals final,initRun,?_,relation,codeEq,finalFfi⟩
  have bodyRun' : evalCrepSemHOLProgExact {decClockCrepSemHOL post with locals := HolFiniteMapExact.empty}
      (compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) =
      (some (.return [.word 8]),final) := by simpa [decClockCrepSemHOL] using bodyRun
  have emptyUpdate : (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab 64)).updateList [] = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp [HolFiniteMapExact.lookup_updateList,FUPDATE_LIST_nil,HolFiniteMapExact.lookup_empty]
  simp only [decClockCrepSemHOL] at bodyRun'
  rw [evalCrepSemHOLProgExact_call_holShape]
  simp [lookupCodeFiniteHOL,found,clock,bodyRun',crepReturnInfoNodupError,emptyUpdate,decClockCrepSemHOL]


def globalStructActualInit : CrepProgHOL 64 := compileProgExactHOLW globalStructCrepContext
    (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)
/-- The executable source wrapper matches the actual generated entry. -/
def pairWrapper : Prog (RiscV.Word 64) :=
  .seq (.seq (.assign .global "pair" (.rStruct [.const 0,.const 0])) .skip)
    (.call none (toStringOfBytes (newMainNameHOL globalStructProgram)) [])

theorem pairWrapper_supported : GlobalCallSupportedIn pairShapeMap [] pairWrapper := by
  unfold pairWrapper
  refine .seq (.seq (.assignGlobalStruct "pair" [.one,.one] (by simp [pairShapeMap]) ?_) (.base .skip)) (.tail _ [] (by simp))
  intro e member
  simp at member
  rcases member with rfl | rfl; exact .scalar (.local (.const _))

theorem pairWrapper_lowered : compileProgExactHOL globalStructContext (progToHOL pairWrapper) =
    .seq (.seq (.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 0,.const 0])) .skip)
      (.call none (newMainNameHOL globalStructProgram) []) := by
  simp only [pairWrapper,progToHOL,expToHOL,compileProgExactHOL,compileExpExactHOL,
    compileExpExactHOLList,globalStruct_pairLookup,ofString_toStringOfBytes,List.map]
theorem pairWrapper_compiled : compileProgExactHOLW globalStructCrepContext
    (compileProgExactHOL globalStructContext (progToHOL pairWrapper)) =
      .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) []) := by
  rw [pairWrapper_lowered, ← globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,globalStructActualInit]


theorem pairWrapper_Supported : Supported pairShapeMap pairWrapper := by
  refine ⟨pairWrapper_supported,?_⟩
  simp only [pairWrapper,ProgByteRanged,ExpByteRanged,ListExpByteRanged,and_true]
  exact ⟨by decide,nameRanged_toStringOfBytes_bridge _,by simp⟩


def globalStructActualBody : CrepProgHOL 64 :=
  compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))
def globalStructActualEntryLimit : Nat :=
  2 + SteppedFlapjack.CrepSteps.statementWeight globalStructActualInit + SteppedFlapjack.CrepSteps.statementWeight globalStructActualBody

theorem globalStruct_actualEntry_run : ∃ (h : 0 < globalStructCallPrograms.length), ∃ (final : CrepSemHOLState 64 Unit),
    evalCrepSemHOLProgExact globalStructCallCrep (globalStructCallPrograms[0]'h).2.2 =
      (some (.return [.word 8]),final) ∧
    SteppedFlapjack.CrepSteps.steps (globalStructCallPrograms[0]'h).2.2 globalStructCallCrep ≤ globalStructActualEntryLimit ∧ final.ffi = sourceFfi := by
  obtain ⟨post,final,initRun,callRun,relation,codeEq,finalFfi⟩ := globalStruct_actualTail_run
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
  have entryEq : (globalStructCallPrograms[0]'h).2.2 = .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) []) := by
    have bodyEq := congrArg Prod.snd (congrArg Prod.snd entry)
    change (globalStructCallPrograms[0]'h).2.2 = _ at bodyEq
    rw [ctxtEq] at bodyEq
    exact bodyEq
  change evalCrepSemHOLProgExact globalStructCallCrep globalStructActualInit = (none,post) at initRun
  have found : post.code.lookup (newMainNameHOL globalStructProgram) = some ([],globalStructActualBody) := by
    rw [codeEq]
    exact globalStruct_actualCrep_lookup
  have clock : post.clock ≠ 0 := by
    have h := relation.2.2.2.2.2.1
    simp [globalStructCallPan] at h
    omega
  have initStatic : SteppedFlapjack.CrepSteps.StaticProgram globalStructActualInit := by
    apply frontendLoopFree_static (globalStruct_initializer_frontend globalStructStart)
    exact globalCompile_initializers_noWhile _ _
  have bodyStatic : SteppedFlapjack.CrepSteps.StaticProgram globalStructActualBody := by
    apply frontendLoopFree_static globalStruct_frontend
    rw [globalStructWitness_lowering]
    rfl
  refine ⟨h,final,?_,?_,finalFfi⟩
  · rw [entryEq,evalCrepSemHOLProgExact_seq_holShape]
    simp only [initRun,callRun,↓reduceIte]
  · rw [entryEq,SteppedFlapjack.CrepSteps.steps_seq]
    rw [initRun]
    simp only
    rw [SteppedFlapjack.CrepSteps.steps_call_tail (newMainNameHOL globalStructProgram) [] post [] [] globalStructActualBody
      (by rfl) found (by rfl) (by simp) clock]
    have i := SteppedFlapjack.CrepSteps.staticProgram_statementWeight initStatic globalStructCallCrep
    have b := SteppedFlapjack.CrepSteps.staticProgram_statementWeight bodyStatic
      (decClockCrepSemHOL {post with locals := HolFiniteMapExact.empty.updateList (List.zip [] [])})
    unfold globalStructActualEntryLimit
    omega

end SteppedFlapjack.Concrete
