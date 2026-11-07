import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.CrepSteps.Defs

/-! The concrete comparison body executes at the Crep level. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

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

end SteppedFlapjack.Concrete
