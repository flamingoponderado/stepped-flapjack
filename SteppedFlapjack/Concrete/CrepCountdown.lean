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

def countdownCrepCallee (n : Nat) : CrepSemHOLState 64 Unit :=
  decClockCrepSemHOL {crepState (countdownHOL n) with locals := HolFiniteMapExact.empty.updateList []}

/-- The countdown's actual generated callee satisfies the general Crep span
with the concrete source bound `6*n+9`. -/
theorem countdown_callee_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ sourceFinal targetResult targetFinal,
      (countdownPanEntry n).evaluateHOLFiniteState (countdownHOL n) =
        (some (.returned (.val (.word 0))),sourceFinal) ∧
      evalCrepSemHOLProgExact (countdownCrepCallee n)
        (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n)) = (targetResult,targetFinal) ∧
      pcCompileCorrectResultRel (countdownCalleeContext n) sourceFinal targetFinal
        (some (.returned (.val (.word 0)))) targetResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n))
        (countdownCrepCallee n) ≤
        sizeOf (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n)) * (6*n+9) := by
  have relations := supported_callee_relations (countdown n) (countdown_supported n)
  simp only [← countdown_hol_eq] at relations
  obtain ⟨_,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  obtain ⟨sourceFinal,sourceRun,sourceBound⟩ := countdown_callee_source n range context primitive handler
  have shape := countdown_frontend_shape n (countdownCalleeContext n)
  have span := frontend_correct_with_steps (countdownCalleeContext n) (countdownHOL n) shape
    (countdownPanEntry n) sourceFinal (some (.returned (.val (.word 0)))) (countdownCrepCallee n) (6*n+9)
    sourceRun (by simp) sourceBound stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  exact ⟨sourceFinal,targetResult,targetFinal,sourceRun,targetRun,resultRel,bound⟩

/-- The actual generated main function calls the renamed countdown callee. -/
def countdownCrepEntry (n : Nat) : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (countdownHOL n)) [])

theorem countdownCrepEntry_generated (n : Nat) :
    (ofString "main",[],countdownCrepEntry n) ∈ crepPrograms (countdownHOL n) := by
  rw [countdown_crep_code]
  simp [countdownCrepEntry]

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
  have relations := supported_callee_relations (countdown n) (countdown_supported n)
  simp only [← countdown_hol_eq] at relations
  obtain ⟨lookup,_,_,_,_,_⟩ := relations
  have lookup' : (crepState (countdownHOL n)).code.lookup (entryName (countdownHOL n)) =
      some ([],compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n)) := lookup
  have nonzero : (crepState (countdownHOL n)).clock ≠ 0 := by
    simp [crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  obtain ⟨sourceFinal,targetResult,targetFinal,_,targetRun,resultRel,bound⟩ :=
    countdown_callee_crep n range context primitive handler
  have returned : targetResult = some (.return [.word 0]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  have wrapper := CrepSteps.tail_entry_returned_word (crepState (countdownHOL n))
    (entryName (countdownHOL n)) (compileProgExactHOLW (countdownCalleeContext n) (countdownHOL n))
    0 targetFinal _ lookup' nonzero (by simpa [countdownCrepCallee,flattenHOL] using targetRun) bound
  exact ⟨targetFinal.emptyLocals,by simpa [countdownCrepEntry] using wrapper.1,
    by simpa [countdownCrepEntry] using wrapper.2⟩

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

def naturalCrepCallee (n : Nat) : CrepSemHOLState 64 Unit :=
  decClockCrepSemHOL {crepState (naturalCountdownHOL n) with locals := HolFiniteMapExact.empty.updateList []}

/-- The natural countdown's compiled callee follows from the general span and
its exact counted source budget. -/
theorem natural_countdown_callee_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ sourceFinal targetResult targetFinal,
      (naturalPanEntry n).evaluateHOLFiniteState (naturalCountdownHOL n) =
        (some (.returned (.val (.word 0))),sourceFinal) ∧
      evalCrepSemHOLProgExact (naturalCrepCallee n)
        (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) = (targetResult,targetFinal) ∧
      pcCompileCorrectResultRel (naturalCalleeContext n) sourceFinal targetFinal
        (some (.returned (.val (.word 0)))) targetResult ∧
      CrepSteps.steps (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n))
        (naturalCrepCallee n) ≤
        sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+7) := by
  have relations := supported_callee_relations (naturalCountdown n) (naturalCountdown_supported n)
  change _ ∧ _ ∧ panToCrepStateRelFiniteExact (naturalPanEntry n) (naturalCrepCallee n) ∧ _ at relations
  obtain ⟨_,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  obtain ⟨_,sourceFinal,_,sourceRun,sourceBound⟩ := natural_countdown_callee_source n range context primitive handler
  have shape := supported_frontend_shape (naturalCountdown_supported n) (naturalCalleeContext n)
  have span := frontend_correct_with_steps (naturalCalleeContext n) (naturalCountdownHOL n) shape
    (naturalPanEntry n) sourceFinal (some (.returned (.val (.word 0)))) (naturalCrepCallee n) (6*n+7)
    sourceRun (by simp) sourceBound stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  exact ⟨sourceFinal,targetResult,targetFinal,sourceRun,targetRun,resultRel,bound⟩

/-- The generated entry for the unprefixed countdown. -/
def naturalCrepEntry (n : Nat) : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (naturalCountdownHOL n)) [])

theorem naturalCrepEntry_generated (n : Nat) :
    (ofString "main",[],naturalCrepEntry n) ∈ crepPrograms (naturalCountdownHOL n) := by
  rw [natural_countdown_crep_code]
  simp [naturalCrepEntry]

/-- The unprefixed countdown entry inherits the exact `6*n+7` source budget. -/
theorem natural_countdown_entry_crep (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),targetFinal) ∧
      CrepSteps.steps (naturalCrepEntry n) (crepState (naturalCountdownHOL n)) ≤
        3 + sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+7) := by
  have relations := supported_callee_relations (naturalCountdown n) (naturalCountdown_supported n)
  have lookup : (crepState (naturalCountdownHOL n)).code.lookup (entryName (naturalCountdownHOL n)) =
      some ([],compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) := relations.1
  have nonzero : (crepState (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  obtain ⟨_,targetResult,targetFinal,_,targetRun,resultRel,bound⟩ :=
    natural_countdown_callee_crep n range context primitive handler
  have returned : targetResult = some (.return [.word 0]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  have wrapper := CrepSteps.tail_entry_returned_word (crepState (naturalCountdownHOL n))
    (entryName (naturalCountdownHOL n)) (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n))
    0 targetFinal _ lookup nonzero (by simpa [naturalCrepCallee,flattenHOL] using targetRun) bound
  exact ⟨targetFinal.emptyLocals,by simpa [naturalCrepEntry] using wrapper.1,
    by simpa [naturalCrepEntry] using wrapper.2⟩

end SteppedFlapjack.Concrete
