import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.Concrete.FrontendState
import SteppedFlapjack.Concrete.SupportedSpan
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge

/-! Concrete countdown at the compiler-generated callee entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def countdownPanEntry (n : Nat) : PanSemStateFiniteExact 64 Unit :=
  callEntryStateHOLFinite (loweredState (countdownHOL n)) HolFiniteMapExact.empty

instance (n : Nat) : DecidablePred (countdownPanEntry n).memaddrs := by
  change DecidablePred ordinaryAddress
  infer_instance

instance (n : Nat) : DecidablePred (countdownPanEntry n).shMemaddrs := by
  change DecidablePred sharedAddress
  infer_instance

/-- A related executable source state is constructed from the actual callee. -/
noncomputable def countdownPanExec (n : Nat) : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  panSemExecStateOfHOL (countdownPanEntry n) (sourceFfiState sourceFfi)

/-- The generated Pancake callee returns zero with at most `6*n+9` source
control visits, using only the countdown parameter range. -/
theorem countdown_callee_source (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      (countdownPanEntry n).evaluateHOLFiniteState (countdownHOL n) =
        (some (.returned (.val (.word 0))),final) ∧
      controlSteps (countdownHOL n) (countdownPanEntry n) ≤ 6*n+9 := by
  have ffiRel : FfiStateRel (sourceFfiState sourceFfi) (countdownPanEntry n).ffi := by
    simpa [countdownPanEntry,callEntryStateHOLFinite,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate] using sourceFfiState_rel sourceFfi
  have rel : PanSemStateRelExec (countdownPanExec n) (countdownPanEntry n).toExact :=
    panSemExecStateOfHOL_rel _ _ ffiRel
  have ranged : PanSemStateRelExecRanged (countdownPanExec n) := panSemExecStateOfHOL_ranged _ _
  have clock : n ≤ (countdownPanEntry n).clock := by
    simp [countdownPanEntry,callEntryStateHOLFinite,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
    omega
  have result := counted_decl_countdown_return n (countdownPanExec n) (countdownPanEntry n)
    rel ranged "x" countdown_name_ranged range clock 0
    (mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty)
    context primitive handler [] 0
  obtain ⟨_,final,_,run,bound,_,_⟩ := result
  exact ⟨final,by simpa [countdownHOL] using run,by simpa [countdownHOL] using bound⟩

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
        3 + sizeOf (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n)) * (6*n+9) := by
  obtain ⟨sourceFinal,run,bound⟩ := countdown_callee_source n range context primitive handler
  have span := supported_entry_crep_return (countdown n) (countdown_supported n) sourceFinal 0 (6*n+9)
    (by simpa [← countdown_hol_eq,countdownPanEntry] using run)
    (by simpa [← countdown_hol_eq,countdownPanEntry] using bound)
  simpa [← countdown_hol_eq,countdownCalleeContext,countdownCrepEntry] using span

/-- The natural unprefixed source countdown and its actual generated callee. -/
def naturalPanEntry (n : Nat) : PanSemStateFiniteExact 64 Unit :=
  callEntryStateHOLFinite (loweredState (naturalCountdownHOL n)) HolFiniteMapExact.empty

instance (n : Nat) : DecidablePred (naturalPanEntry n).memaddrs := by
  change DecidablePred ordinaryAddress
  infer_instance

instance (n : Nat) : DecidablePred (naturalPanEntry n).shMemaddrs := by
  change DecidablePred sharedAddress
  infer_instance

noncomputable def naturalPanExec (n : Nat) : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  panSemExecStateOfHOL (naturalPanEntry n) (sourceFfiState sourceFfi)

/-- Reuse the existing exact `6*n+7` counted proof at the generated callee. -/
theorem natural_countdown_callee_source (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler (naturalPanExec n).structs []
        (naturalPanExec n).baseAddress (naturalPanExec n).topAddress panSemBitVec64BytesInWord (n+3)
        (naturalPanExec n).locals (naturalPanExec n).globals (naturalPanExec n).memory (naturalPanExec n).ffi
        (naturalCountdown n) (memoryAccess := some (panSemBitVec64MemoryAccess (naturalPanExec n))) =
          some (result,6*n+7) ∧
      (naturalPanEntry n).evaluateHOLFiniteState (naturalCountdownHOL n) =
        (some (.returned (.val (.word 0))),final) ∧
      controlSteps (naturalCountdownHOL n) (naturalPanEntry n) ≤ 6*n+7 := by
  have ffiRel : FfiStateRel (sourceFfiState sourceFfi) (naturalPanEntry n).ffi := by
    simpa [naturalPanEntry,callEntryStateHOLFinite,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate] using sourceFfiState_rel sourceFfi
  have rel : PanSemStateRelExec (naturalPanExec n) (naturalPanEntry n).toExact :=
    panSemExecStateOfHOL_rel _ _ ffiRel
  have ranged : PanSemStateRelExecRanged (naturalPanExec n) := panSemExecStateOfHOL_ranged _ _
  have clock : n ≤ (naturalPanEntry n).clock := by
    simp [naturalPanEntry,callEntryStateHOLFinite,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
    omega
  have result := counted_decl_countdown_simplified n (naturalPanExec n) (naturalPanEntry n)
    rel ranged "x" countdown_name_ranged range clock 0 context primitive handler [] 0
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
        3 + sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+7) := by
  obtain ⟨_,sourceFinal,_,run,bound⟩ := natural_countdown_callee_source n range context primitive handler
  have span := supported_entry_crep_return (naturalCountdown n) (naturalCountdown_supported n)
    sourceFinal 0 (6*n+7) run bound
  simpa [naturalCountdownHOL,naturalCalleeContext,naturalCrepEntry] using span

end SteppedFlapjack.Concrete
