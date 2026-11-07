import SteppedFlapjack.Concrete.CountedApplications
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def badShift : Prog (RiscV.Word 64) := .return (.shift .lsl (.const 1) (.const 64))
theorem badShift_supported : Supported badShift := by
  constructor
  · exact .ret (.shift .lsl (.const _) (.const _))
  · simp [badShift,ProgByteRanged,ExpByteRanged]
theorem badShift_source_run (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL badShift)).structs []
      (executableState (progToHOL badShift)).baseAddress (executableState (progToHOL badShift)).topAddress
      panSemBitVec64BytesInWord 1 (executableState (progToHOL badShift)).locals (executableState (progToHOL badShift)).globals
      (executableState (progToHOL badShift)).memory (executableState (progToHOL badShift)).ffi badShift
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL badShift)))) =
      some (.error (executableState (progToHOL badShift)).locals (executableState (progToHOL badShift)).globals
        (executableState (progToHOL badShift)).memory (executableState (progToHOL badShift)).ffi,0) := by
  simp [badShift,evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,evalPanValueExpCounted,
    evalPanValueExp,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,
    panSemWordModel,RiscV.panRiscVMemoryModel,RiscV.panRiscVShift]
theorem badShift_simp : panSimpProg badShift = badShift := by
  simp [badShift,panSimpProg,seqAssoc,smartSeq,retToTail]

theorem badShift_code : crepPrograms (progToHOL badShift) =
    [(ofString "main",[],.seq .skip (.call none (entryName (progToHOL badShift)) [])),
      (entryName (progToHOL badShift),[],.return [.shift .lsl (.const 1) (.const 64)])] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp only [badShift,progToHOL,expToHOL]
  simp_crep_code
theorem badShift_target_body {σ : Type} (state : CrepSemHOLState 64 σ) :
    evalCrepSemHOLProgExact state (.return [.shift .lsl (.const 1) (.const 64)]) = (some .error,state) := by
  rw [evalCrepSemHOLProgExact_return]
  simp [evalCrepSemHOLExp,wordShiftHOL]

theorem badShift_target_entry : ∃ final,
    evalCrepSemHOLProgExact (crepState (progToHOL badShift))
      (.seq .skip (.call none (entryName (progToHOL badShift)) [])) = (some .error,final) := by
  let state := crepState (progToHOL badShift)
  have lookup : state.code.lookup (entryName (progToHOL badShift)) =
      some ([],.return [.shift .lsl (.const 1) (.const 64)]) := by
    exact generated_callee_lookup (progToHOL badShift) _ badShift_code
  have nonzero : state.clock ≠ 0 := by
    simp [state,crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  rw [evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
  simp only [if_true]
  rw [evalCrepSemHOLProgExact_call_holShape]
  change (crepState (progToHOL badShift)).code.lookup (entryName (progToHOL badShift)) = _ at lookup
  change (crepState (progToHOL badShift)).clock ≠ 0 at nonzero
  simp [lookupCodeFiniteHOL,lookup,crepReturnInfoNodupError,nonzero]
  simp [evalCrepSemHOLProgExact_return,evalCrepSemHOLExp,wordShiftHOL]
theorem badShift_target_steps :
    SteppedFlapjack.CrepSteps.steps (.seq .skip (.call none (entryName (progToHOL badShift)) []))
      (crepState (progToHOL badShift)) = 4 := by
  let state := crepState (progToHOL badShift)
  have lookup : state.code.lookup (entryName (progToHOL badShift)) =
      some ([],.return [.shift .lsl (.const 1) (.const 64)]) := by
    exact generated_callee_lookup (progToHOL badShift) _ badShift_code
  have nonzero : state.clock ≠ 0 := by
    simp [state,crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  have call := SteppedFlapjack.CrepSteps.steps_call_tail (entryName (progToHOL badShift)) [] state [] []
    (.return [.shift .lsl (.const 1) (.const 64)]) (by simp) lookup (by simp) (by simp) nonzero
  rw [SteppedFlapjack.CrepSteps.steps_seq]
  simp only [evalCrepSemHOLProgExact_skip]
  rw [call]
  have one : SteppedFlapjack.CrepSteps.steps (.skip : CrepProgHOL 64) state = 1 :=
    SteppedFlapjack.CrepSteps.steps_leaf _ _ rfl
  rw [one]
  rw [SteppedFlapjack.CrepSteps.steps_leaf]
  rfl

example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    (exactState (progToHOL badShift)).evaluateHOLFiniteState (progToHOL badShift) =
      (some .error,exactState (progToHOL badShift)) ∧
    controlSteps (progToHOL badShift) (exactState (progToHOL badShift)) = 1 := by
  have words : WordLocals (executableState (progToHOL badShift)).locals := by
    intro name value found
    simp [executableState,singleEntrySourceProduction,sourceProduction] at found
  have run := badShift_source_run context primitive handler
  have result := counted_scalar_return_error (scope := []) (executableState (progToHOL badShift)) (exactState (progToHOL badShift))
    (source_related _) (source_ranged _) words (.shift .lsl (.const 1) (.const 64))
    (.shift .lsl (.const _) (.const _)) (by simp [ExpByteRanged]) context primitive handler [] 1 0
    (by simpa [badShift] using run)
  simpa [badShift,progToHOL] using result.2
theorem badShift_simp_source :
    panSimpSourceState badShift (exactState (progToHOL badShift)) = exactState (progToHOL badShift) := by
  simp [panSimpSourceState,badShift_simp,exactState,singleEntrySourceTemplate]

example : ∃ final,
    evalCrepSemHOLProgExact
      (crepStateFrom (panSimpSourceState badShift (exactState (progToHOL badShift))) (progToHOL (panSimpProg badShift)))
      (.seq .skip (.call none (entryName (progToHOL (panSimpProg badShift))) [])) = (some .error,final) ∧
    SteppedFlapjack.CrepSteps.steps (.seq .skip (.call none (entryName (progToHOL (panSimpProg badShift))) []))
      (crepStateFrom (panSimpSourceState badShift (exactState (progToHOL badShift))) (progToHOL (panSimpProg badShift))) = 4 := by
  obtain ⟨final,run⟩ := badShift_target_entry
  refine ⟨final,?_,?_⟩
  · simpa [badShift_simp,badShift_simp_source,crepStateFrom,loweredStateFrom,crepState,loweredState] using run
  · simpa [badShift_simp,badShift_simp_source,crepStateFrom,loweredStateFrom,crepState,loweredState] using badShift_target_steps

/-- The general all-outcomes theorem applies to an actual source error. -/
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := clockedFixtureSource badShift 1
    let body := progToHOL (panSimpProg badShift)
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ final, evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState badShift source) body) entry = (some .error,final) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState badShift source) body) ≤ 34659 := by
  let source := clockedFixtureSource badShift 1
  let production := clockedFixtureProduction badShift 1
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have rel : PanSemStateRelExec production source.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL badShift)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have ranged : PanSemStateRelExecRanged production :=
    PanSemStateRelExecRanged.setClock (source_ranged (progToHOL badShift)) 1
  have words : WordLocals production.locals := by
    intro name value found
    simp [production,clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found
  have run := badShift_source_run context primitive handler
  have run' : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress
      production.topAddress panSemBitVec64BytesInWord 1 production.locals production.globals production.memory production.ffi badShift
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.error production.locals production.globals production.memory production.ffi,0) := by
    simpa [production,clockedFixtureProduction,panSemBitVec64MemoryAccess] using run
  obtain ⟨exit,final,outcome,target,bound⟩ := supported_counted_full_frontend_uniform badShift badShift_supported production source
    rel ranged words rfl rfl rfl rfl context primitive handler [] 1 0 1 _ run' (by omega) rfl
  cases outcome with
  | error l g m f =>
    have size : sizeOf (compileProgExactHOLW
        (ctxtFcExactHOL (frontendContext (progToHOL (panSimpProg badShift))).funcs
          (frontendContext (progToHOL (panSimpProg badShift))).eids [] [] [])
        (progToHOL (panSimpProg badShift))) = 76 := by decide +kernel
    refine ⟨final,target,?_⟩
    simpa [size] using bound
end SteppedFlapjack.Concrete
