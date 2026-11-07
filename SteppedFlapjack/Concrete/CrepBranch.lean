import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.CrepSteps.Defs
import SteppedFlapjack.Concrete.SupportedSpan

/-! The concrete comparison body executes at the Crep level. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def branchCrepBody : CrepProgHOL 64 :=
  .ite (.cmp .lower (.const 0) (.const 1)) (.return [.const 7]) (.return [.const 9])

/-- The generated comparison body returns seven from any Crep state. -/
theorem branchCrepBody_run {σ : Type} (state : CrepSemHOLState 64 σ) :
    evalCrepSemHOLProgExact state branchCrepBody =
      (some (.return [.word 7]),state.emptyLocals) := by
  rw [branchCrepBody,evalCrepSemHOLProgExact_ite_holShape]
  simp [evalCrepSemHOLExp,Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    evalCrepSemHOLProgExact_return]

/-- A Crep conditional and its selected return cost two evaluator visits. -/
theorem branchCrepBody_steps {σ : Type} (state : CrepSemHOLState 64 σ) :
    SteppedFlapjack.CrepSteps.steps branchCrepBody state = 2 := by
  rw [branchCrepBody,SteppedFlapjack.CrepSteps.steps_ite]
  simp [evalCrepSemHOLExp,Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    SteppedFlapjack.CrepSteps.steps_leaf]

/-- The actual generated code table contains the comparison body. -/
theorem branchCrepCode_lookup :
    (crepState branchingHOL).code.lookup (entryName branchingHOL) = some ([],branchCrepBody) := by
  have fresh : entryName branchingHOL ≠ ofString "main" := by
    intro same
    have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
      ((functionsHOL (singleEntryProgram (ofString "main") branchingHOL)).map Prod.fst)
    apply notMem
    simpa [entryName,newMainNameHOL,singleEntryProgram,functionsHOL] using same
  simp [crepState,concreteDeclCrepState,branching_crep_code,alistToFmapCodeExact,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,branchCrepBody,Ne.symm fresh]

/-- The generated entry wrapper makes a tail call to the comparison body. -/
def branchCrepEntry : CrepProgHOL 64 := .seq .skip (.call none (entryName branchingHOL) [])

/-- The entry proved below is exactly the compiler-generated main function. -/
theorem branchCrepEntry_generated :
    (ofString "main",[],branchCrepEntry) ∈ crepPrograms branchingHOL := by
  rw [branching_crep_code]
  simp [branchCrepEntry]

/-- The complete generated entry visits five Crep statements. -/
theorem branchCrepEntry_steps :
    SteppedFlapjack.CrepSteps.steps branchCrepEntry (crepState branchingHOL) = 5 := by
  let state := crepState branchingHOL
  have nonzero : state.clock ≠ 0 := by
    simp [state,crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  have call := SteppedFlapjack.CrepSteps.steps_call_tail (entryName branchingHOL) [] state [] [] branchCrepBody
    (by simp) branchCrepCode_lookup (by simp) (by simp) nonzero
  rw [branchCrepEntry,SteppedFlapjack.CrepSteps.steps_seq]
  simp only [evalCrepSemHOLProgExact_skip]
  rw [call,branchCrepBody_steps]
  have one : SteppedFlapjack.CrepSteps.steps (.skip : CrepProgHOL 64) state = 1 :=
    SteppedFlapjack.CrepSteps.steps_leaf _ _ rfl
  rw [one]

/-- The generated wrapper reaches the comparison body and returns seven. -/
theorem branchCrepEntry_run :
    ∃ final, evalCrepSemHOLProgExact (crepState branchingHOL) branchCrepEntry =
      (some (.return [.word 7]),final) := by
  let state := crepState branchingHOL
  have nonzero : state.clock ≠ 0 := by
    simp [state,crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  rw [branchCrepEntry,evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
  simp only [if_true]
  rw [evalCrepSemHOLProgExact_call_holShape]
  change (crepState branchingHOL).clock ≠ 0 at nonzero
  simp [lookupCodeFiniteHOL,branchCrepCode_lookup,crepReturnInfoNodupError,nonzero,branchCrepBody_run]

/-- The comparison body has the same source run at the generated callee. -/
theorem branching_callee_source :
    (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty).evaluateHOLFiniteState branchingHOL =
      (some (.returned (.val (.word 7))),
        (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty).emptyLocalsHOLFinite) ∧
    controlSteps branchingHOL (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty) ≤ 6 := by
  constructor
  · rw [branchingHOL,PanSemStateFiniteExact.evaluateHOLFiniteState_ite]
    simp [PanSemStateFiniteExact.evaluateHOLFiniteState_return,
      evalHOLExact,shapeOfHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [branchingHOL,controlSteps.eq_def,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    split <;> omega

def branchCalleeContext : PanToCrepContextExact 64 :=
  let caller := frontendContext branchingHOL
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

def branchCrepCallee : CrepSemHOLState 64 Unit :=
  decClockCrepSemHOL {crepState branchingHOL with locals := HolFiniteMapExact.empty.updateList []}

/-- The general frontend span establishes the actual comparison callee run. -/
theorem branching_callee_span :
    ∃ targetResult targetFinal,
      evalCrepSemHOLProgExact branchCrepCallee (compileProgExactHOLW branchCalleeContext branchingHOL) =
        (targetResult,targetFinal) ∧
      pcCompileCorrectResultRel branchCalleeContext
        (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty).emptyLocalsHOLFinite
        targetFinal (some (.returned (.val (.word 7)))) targetResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW branchCalleeContext branchingHOL) branchCrepCallee ≤
        sizeOf (compileProgExactHOLW branchCalleeContext branchingHOL) * 6 := by
  have relations := supported_callee_relations branching branching_supported
  simp only [← branching_hol_eq] at relations
  obtain ⟨_,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  obtain ⟨sourceRun,sourceBound⟩ := branching_callee_source
  have span := frontend_correct_with_steps branchCalleeContext branchingHOL (branching_frontend_shape _)
    _ _ (some (.returned (.val (.word 7)))) branchCrepCallee 6
    sourceRun (by simp) sourceBound stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  exact ⟨targetResult,targetFinal,targetRun,resultRel,bound⟩

/-- The generated comparison entry bound follows from the general span. -/
theorem branching_entry_span :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState branchingHOL) branchCrepEntry =
        (some (.return [.word 7]),targetFinal) ∧
      SteppedFlapjack.CrepSteps.steps branchCrepEntry (crepState branchingHOL) ≤
        231 := by
  have relations := supported_callee_relations branching branching_supported
  simp only [← branching_hol_eq] at relations
  obtain ⟨lookup,_,_,_,_,_⟩ := relations
  have lookup' : (crepState branchingHOL).code.lookup (entryName branchingHOL) =
      some ([],compileProgExactHOLW branchCalleeContext branchingHOL) := lookup
  have codeEq : compileProgExactHOLW branchCalleeContext branchingHOL = branchCrepBody := by
    rw [branchCrepCode_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have nonzero : (crepState branchingHOL).clock ≠ 0 := by
    simp [crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  obtain ⟨targetResult,targetFinal,targetRun,resultRel,bound⟩ := branching_callee_span
  have returned : targetResult = some (.return [.word 7]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  have wrapper := CrepSteps.tail_entry_returned_word (crepState branchingHOL) (entryName branchingHOL)
    (compileProgExactHOLW branchCalleeContext branchingHOL) 7 targetFinal _ lookup' nonzero (by simpa [branchCrepCallee,flattenHOL] using targetRun) bound
  refine ⟨targetFinal.emptyLocals,by simpa [branchCrepEntry] using wrapper.1,?_⟩
  rw [codeEq] at wrapper
  have size : sizeOf branchCrepBody = 38 := by decide
  rw [size] at wrapper
  simpa [branchCrepEntry] using wrapper.2

/-- Concrete source-to-Crep correspondence, obtained by directly checking
both runs. The five-visit calculation cross-checks the general span bound above. -/
theorem branching_source_crep_correspondence
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState branchingHOL)
        (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty) ∧
      panToCrepStateRelFiniteExact (loweredState branchingHOL) (crepState branchingHOL) ∧
      evalPanValueFfiProgSteps context primitive handler (executableState branchingHOL).structs []
        (executableState branchingHOL).baseAddress (executableState branchingHOL).topAddress
        panSemBitVec64BytesInWord 2 (executableState branchingHOL).locals
        (executableState branchingHOL).globals (executableState branchingHOL).memory
        (executableState branchingHOL).ffi branching
        (memoryAccess := some (panSemBitVec64MemoryAccess (executableState branchingHOL))) =
          some (.returned (executableState branchingHOL).locals (executableState branchingHOL).globals
            (executableState branchingHOL).memory (executableState branchingHOL).ffi [.word 7],6) ∧
      evalCrepSemHOLProgExact (crepState branchingHOL) branchCrepEntry = (some (.return [.word 7]),final) ∧
      SteppedFlapjack.CrepSteps.steps branchCrepEntry (crepState branchingHOL) = 5 := by
  obtain ⟨final,run⟩ := branchCrepEntry_run
  exact ⟨final,branching_globals_related,crep_state_related _,branching_run context primitive handler,
    run,branchCrepEntry_steps⟩

end SteppedFlapjack.Concrete
