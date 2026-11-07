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
  apply generated_callee_lookup branchingHOL branchCrepBody
  simpa [branchCrepBody] using branching_crep_code

/-- The generated entry wrapper makes a tail call to the comparison body. -/
def branchCrepEntry : CrepProgHOL 64 := .seq .skip (.call none (entryName branchingHOL) [])

/-- The entry proved below is exactly the compiler-generated main function. -/
theorem branchCrepEntry_generated :
    (ofString "main",[],branchCrepEntry) ∈ crepPrograms branchingHOL := by
  simpa [branchCrepEntry] using generated_entry_member branchingHOL

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

def branchCalleeContext : PanToCrepContextExact 64 :=
  let caller := frontendContext branchingHOL
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

/-- The generated comparison entry bound follows from the general span. -/
theorem branching_entry_span :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState branchingHOL) branchCrepEntry =
        (some (.return [.word 7]),targetFinal) ∧
      SteppedFlapjack.CrepSteps.steps branchCrepEntry (crepState branchingHOL) ≤
        231 := by
  obtain ⟨run,bound⟩ := branching_hol_run
  have span := supported_original_entry_crep_return_fixture branching branching_supported _ 7 6
    (by simpa [← branching_hol_eq] using run) (by simpa [← branching_hol_eq] using bound)
  have relations := supported_callee_relations branching branching_supported
  simp only [← branching_hol_eq] at relations
  have lookup := relations.1
  have codeEq : compileProgExactHOLW branchCalleeContext branchingHOL = branchCrepBody := by
    rw [branchCrepCode_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf branchCrepBody = 38 := by decide
  simp only [← branching_hol_eq] at span
  change ∃ final,
    evalCrepSemHOLProgExact (crepState branchingHOL) branchCrepEntry =
      (some (.return [.word 7]),final) ∧
    CrepSteps.steps branchCrepEntry (crepState branchingHOL) ≤
      3 + sizeOf (compileProgExactHOLW branchCalleeContext branchingHOL) * 6 at span
  rw [codeEq,size] at span
  simpa using span

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

theorem branching_simp_program : panSimpProg branching = branching := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,branching]

theorem branching_simp_source : panSimpSourceState branching (exactState branchingHOL) = exactState branchingHOL := by
  simp [panSimpSourceState,branching_simp_program,exactState,singleEntrySourceTemplate,← branching_hol_eq]

theorem branching_simp_declarations : panSimpDeclsHOL (declarations branchingHOL) = declarations branchingHOL := by
  simpa [← branching_hol_eq,branching_simp_program] using supported_panSimp_declarations branching branching_supported

theorem branching_panSimp_crep (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ targetFinal,
      evalPanValueFfiProgSteps context primitive handler (executableState branchingHOL).structs []
        (executableState branchingHOL).baseAddress (executableState branchingHOL).topAddress
        panSemBitVec64BytesInWord 2 (executableState branchingHOL).locals
        (executableState branchingHOL).globals (executableState branchingHOL).memory
        (executableState branchingHOL).ffi branching
        (memoryAccess := some (panSemBitVec64MemoryAccess (executableState branchingHOL))) =
          some (.returned (executableState branchingHOL).locals (executableState branchingHOL).globals
            (executableState branchingHOL).memory (executableState branchingHOL).ffi [.word 7],6) ∧
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState branching (exactState branchingHOL))
          (progToHOL (panSimpProg branching))) branchCrepEntry =
        (some (.return [.word 7]),targetFinal) ∧
      CrepSteps.steps branchCrepEntry
        (crepStateFrom (panSimpSourceState branching (exactState branchingHOL))
          (progToHOL (panSimpProg branching))) ≤ 231 := by
  obtain ⟨targetFinal,targetRun,targetBound⟩ := branching_entry_span
  refine ⟨targetFinal,branching_run context primitive handler,?_,?_⟩
  · simpa [branching_simp_source,branching_simp_program,← branching_hol_eq,
      crepStateFrom,loweredStateFrom,crepState,loweredState] using targetRun
  · simpa [branching_simp_source,branching_simp_program,← branching_hol_eq,
      crepStateFrom,loweredStateFrom,crepState,loweredState] using targetBound
end SteppedFlapjack.Concrete
