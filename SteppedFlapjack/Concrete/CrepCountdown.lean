import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.Concrete.FrontendState
import SteppedFlapjack.Concrete.SupportedSpan
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge

/-! Concrete countdown at the compiler-generated callee entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

/-- The actual compiler-selected callee context and Crep entry state. -/
def countdownCalleeContext (n : Nat) : PanToCrepContextExact 64 :=
  let caller := frontendContext (countdownHOL n)
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

/-- The actual generated main function calls the renamed countdown callee. -/
def countdownCrepEntry (n : Nat) : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (countdownHOL n)) [])

theorem countdownCrepEntry_generated (n : Nat) :
    (ofString "main",[],countdownCrepEntry n) ∈ crepPrograms (countdownHOL n) := by
  simpa [countdownCrepEntry] using generated_entry_member (countdownHOL n)

/-- The generated Crep entry has an explicit visit bound obtained from the
countdown source bound and the general frontend span. -/
theorem countdown_entry_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState (countdownHOL n)) (countdownCrepEntry n) =
        (some (.return [.word 0]),targetFinal) ∧
      SteppedFlapjack.CrepSteps.steps (countdownCrepEntry n) (crepState (countdownHOL n)) ≤
        3 + (n+38) * (6*n+9) := by
  obtain ⟨_,sourceFinal,_,run,bound,_⟩ := countdown_run n range context primitive handler
  have span := supported_original_entry_crep_return_fixture (countdown n) (countdown_supported n) sourceFinal 0 (6*n+9)
    (by simpa [← countdown_hol_eq] using run)
    (by simpa [← countdown_hol_eq] using bound)
  have lookup := (supported_callee_relations (countdown n) (countdown_supported n)).1
  simp only [← countdown_hol_eq] at lookup
  have actual := generated_callee_lookup (countdownHOL n) (countdownCrepBody (BitVec.ofNat 64 n)) (countdown_crep_code n)
  have codeEq : compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n) =
      countdownCrepBody (BitVec.ofNat 64 n) := by
    rw [actual] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf (countdownCrepBody (BitVec.ofNat 64 n)) = n+38 := by
    have h := (countdownCrepBody_sizes (BitVec.ofNat 64 n)).1
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt range] at h
    exact h
  simp only [← countdown_hol_eq] at span
  change ∃ final,
    evalCrepSemHOLProgExact (crepState (countdownHOL n)) (countdownCrepEntry n) =
      (some (.return [.word 0]),final) ∧
    CrepSteps.steps (countdownCrepEntry n) (crepState (countdownHOL n)) ≤
      3 + sizeOf (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n)) * (6*n+9) at span
  rw [codeEq,size] at span
  exact span

/-- The natural unprefixed countdown has exact source cost `6*n+7`. -/
theorem natural_countdown_source (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler (executableState (naturalCountdownHOL n)).structs []
        (executableState (naturalCountdownHOL n)).baseAddress (executableState (naturalCountdownHOL n)).topAddress panSemBitVec64BytesInWord (n+3)
        (executableState (naturalCountdownHOL n)).locals (executableState (naturalCountdownHOL n)).globals (executableState (naturalCountdownHOL n)).memory (executableState (naturalCountdownHOL n)).ffi
        (naturalCountdown n) (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (naturalCountdownHOL n)))) =
          some (result,6*n+7) ∧
      (exactState (naturalCountdownHOL n)).evaluateHOLFiniteState (naturalCountdownHOL n) =
        (some (.returned (.val (.word 0))),final) ∧
      controlSteps (naturalCountdownHOL n) (exactState (naturalCountdownHOL n)) ≤ 6*n+7 := by
  have result := counted_decl_countdown_simplified n (executableState (naturalCountdownHOL n))
    (exactState (naturalCountdownHOL n)) (source_related _) (source_ranged _)
    "x" countdown_name_ranged range (by change n ≤ 2^64; omega) 0 context primitive handler [] 0
  obtain ⟨result,final,exec,run,bound,_⟩ := result
  exact ⟨result,final,by simpa [naturalCountdown] using exec,
    by simpa [naturalCountdownHOL,naturalCountdown,progToHOL,expToHOL,shapeToHOL,countdownBody,countdownBodyHOL] using run,
    by simpa [naturalCountdownHOL,naturalCountdown,progToHOL,expToHOL,shapeToHOL,countdownBody,countdownBodyHOL] using bound⟩

def naturalCalleeContext (n : Nat) : PanToCrepContextExact 64 :=
  let caller := frontendContext (naturalCountdownHOL n)
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

/-- The generated entry for the unprefixed countdown. -/
def naturalCrepEntry (n : Nat) : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (naturalCountdownHOL n)) [])

theorem naturalCrepEntry_generated (n : Nat) :
    (ofString "main",[],naturalCrepEntry n) ∈ crepPrograms (naturalCountdownHOL n) := by
  simpa [naturalCrepEntry] using generated_entry_member (naturalCountdownHOL n)

/-- The unprefixed countdown entry inherits the exact `6*n+7` source budget. -/
theorem natural_countdown_entry_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),targetFinal) ∧
      CrepSteps.steps (naturalCrepEntry n) (crepState (naturalCountdownHOL n)) ≤
        3 + (n+36) * (6*n+7) := by
  obtain ⟨_,sourceFinal,_,run,bound⟩ := natural_countdown_source n range context primitive handler
  have span := supported_original_entry_crep_return_fixture (naturalCountdown n) (naturalCountdown_supported n)
    sourceFinal 0 (6*n+7) run bound
  have lookup := (supported_callee_relations (naturalCountdown n) (naturalCountdown_supported n)).1
  change (crepState (naturalCountdownHOL n)).code.lookup (entryName (naturalCountdownHOL n)) =
    some ([],compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) at lookup
  have actual := generated_callee_lookup (naturalCountdownHOL n) (naturalCountdownCrepBody (BitVec.ofNat 64 n))
    (natural_countdown_crep_code n)
  have codeEq : compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n) =
      naturalCountdownCrepBody (BitVec.ofNat 64 n) := by
    rw [actual] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf (naturalCountdownCrepBody (BitVec.ofNat 64 n)) = n+36 := by
    have h := (countdownCrepBody_sizes (BitVec.ofNat 64 n)).2
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt range] at h
    exact h
  change ∃ final,
    evalCrepSemHOLProgExact (crepState (naturalCountdownHOL n)) (naturalCrepEntry n) =
      (some (.return [.word 0]),final) ∧
    CrepSteps.steps (naturalCrepEntry n) (crepState (naturalCountdownHOL n)) ≤
      3 + sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+7) at span
  rw [codeEq,size] at span
  exact span

theorem countdown_simp_declarations (n : Nat) :
 panSimpDeclsHOL (declarations (countdownHOL n)) = declarations (naturalCountdownHOL n) := by
 simp [declarations,singleEntryProgram,panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,
   retToTailHOL,seqCallRetHOL,countdownHOL,naturalCountdownHOL,naturalCountdown,countdownBodyHOL,countdownBody,
   progToHOL,expToHOL,shapeToHOL]

theorem countdown_simp_program (n : Nat) : panSimpProg (countdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,countdown,naturalCountdown,countdownBody]

theorem countdown_simp_source (n : Nat) :
  panSimpSourceState (countdown n) (exactState (countdownHOL n)) = exactState (naturalCountdownHOL n) := by
  simp [panSimpSourceState,countdown_simp_program,exactState,singleEntrySourceTemplate,
    naturalCountdownHOL]


theorem countdown_panSimp_crep_code (n : Nat) :
    compileProgDeclsHOLW (compileTopExactHOL (panSimpDeclsHOL (declarations (countdownHOL n))) (ofString "main")) =
      crepPrograms (naturalCountdownHOL n) := by
  rw [countdown_simp_declarations]
  rfl

/-- The prefixed source countdown reaches the actual pan_simp/global/Crep
entry with a closed-form Crep bound. -/
theorem countdown_panSimp_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ sourceResult targetFinal,
      evalPanValueFfiProgSteps context primitive handler (executableState (countdownHOL n)).structs []
        (executableState (countdownHOL n)).baseAddress (executableState (countdownHOL n)).topAddress
        panSemBitVec64BytesInWord (n+4) (executableState (countdownHOL n)).locals
        (executableState (countdownHOL n)).globals (executableState (countdownHOL n)).memory
        (executableState (countdownHOL n)).ffi (countdown n)
        (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (countdownHOL n)))) =
          some (sourceResult,6*n+9) ∧
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState (countdown n) (exactState (countdownHOL n)))
          (progToHOL (panSimpProg (countdown n)))) (naturalCrepEntry n) =
        (some (.return [.word 0]),targetFinal) ∧
      CrepSteps.steps (naturalCrepEntry n)
        (crepStateFrom (panSimpSourceState (countdown n) (exactState (countdownHOL n)))
          (progToHOL (panSimpProg (countdown n)))) ≤ 3+(n+36)*(6*n+7) := by
  obtain ⟨sourceResult,_,sourceRun,_,_,_⟩ := countdown_run n range context primitive handler
  obtain ⟨targetFinal,targetRun,targetBound⟩ := natural_countdown_entry_crep n range context primitive handler
  refine ⟨sourceResult,targetFinal,sourceRun,?_,?_⟩
  · simpa [countdown_simp_source,countdown_simp_program,naturalCountdownHOL,
      crepStateFrom,loweredStateFrom,crepState,loweredState] using targetRun
  · simpa [countdown_simp_source,countdown_simp_program,naturalCountdownHOL,
      crepStateFrom,loweredStateFrom,crepState,loweredState] using targetBound

end SteppedFlapjack.Concrete
