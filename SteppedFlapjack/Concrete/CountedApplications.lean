import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.Concrete.CrepCountdown
import SteppedFlapjack.Concrete.CrepBranch
import SteppedFlapjack.Concrete.BranchingLoop
/-! The general counted span instantiated for the phase-zero witnesses.
The fixture clocks are the explicit source step budgets, so each target bound
is calculated from that budget and the actual generated Crep body. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

def clockedFixtureSource (program : Prog (RiscV.Word 64)) (n : Nat) :=
  {(exactState (progToHOL program)) with clock := n}
def clockedFixtureProduction (program : Prog (RiscV.Word 64)) (n : Nat) :=
  {(executableState (progToHOL program)) with clock := n}

/-- Specialize the general span to the init-e-shaped fixture at a chosen clock. -/
theorem fixture_counted_span (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL program)).structs []
      (executableState (progToHOL program)).baseAddress (executableState (progToHOL program)).topAddress
      panSemBitVec64BytesInWord fuel (executableState (progToHOL program)).locals
      (executableState (progToHOL program)).globals (executableState (progToHOL program)).memory
      (executableState (progToHOL program)).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL program)))) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (budget : count ≤ n) :
    let body := progToHOL (panSimpProg program)
    let callee := ctxtFcExactHOL (frontendContext body).funcs (frontendContext body).eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ final, evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState program (clockedFixtureSource program n)) body) entry =
      (some (.return [.word word]),final) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState program (clockedFixtureSource program n)) body) ≤
        3 + sizeOf (compileProgExactHOLW callee body) * (sizeOf (compileProgExactHOLW callee body) * (n+1)) := by
  let source := clockedFixtureSource program n
  let production := clockedFixtureProduction program n
  let _ : DecidablePred source.memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  have rel : PanSemStateRelExec production source.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL program)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have ranged : PanSemStateRelExecRanged production :=
    PanSemStateRelExecRanged.setClock (source_ranged (progToHOL program)) n
  have words : WordLocals production.locals := by
    intro name value found
    simp [production,clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found
  have run' : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress
      production.topAddress panSemBitVec64BytesInWord fuel production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count) := by
    simpa [production,clockedFixtureProduction,panSemBitVec64MemoryAccess] using run
  exact supported_counted_full_frontend program supported production source rel ranged words rfl rfl rfl rfl
    context primitive handler [] fuel count n postLocals postGlobals postMemory postFfi word run' budget rfl
private theorem natural_compiled_size (n : Nat) (range : n < 2^64) :
    sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) = n+36 := by
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
  rw [codeEq,size]

/-- The prefixed countdown through the full counted span. -/
theorem countdown_counted_fixture (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9)))
          (naturalCountdownHOL n)) (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      CrepSteps.steps (naturalCrepEntry n)
        (crepStateFrom (panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9)))
          (naturalCountdownHOL n)) ≤ 3 + (n+36)*((n+36)*(6*n+10)) := by
  obtain ⟨result,_,run,_,_,resultEq⟩ := countdown_run n range context primitive handler
  subst result
  have run' : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL (countdown n))).structs []
      (executableState (progToHOL (countdown n))).baseAddress (executableState (progToHOL (countdown n))).topAddress
      panSemBitVec64BytesInWord (n+4) (executableState (progToHOL (countdown n))).locals
      (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
      (executableState (progToHOL (countdown n))).ffi (countdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (countdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (countdown n))).locals "x"))
          (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
          (executableState (progToHOL (countdown n))).ffi [.word 0],6*n+9) := by
    simpa only [← countdown_hol_eq] using run
  have span := fixture_counted_span (countdown n) (countdown_supported n) context primitive handler (n+4) (6*n+9) (6*n+9)
    (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (countdown n))).locals "x"))
    (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
    (executableState (progToHOL (countdown n))).ffi 0 run' (by omega)
  simp only [countdown_simp_program] at span
  have size := natural_compiled_size n range
  change ∃ final, evalCrepSemHOLProgExact
      (crepStateFrom (panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9)))
        (naturalCountdownHOL n)) (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
    CrepSteps.steps (naturalCrepEntry n)
      (crepStateFrom (panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9)))
        (naturalCountdownHOL n)) ≤
    3 + sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) *
      (sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+9+1)) at span
  rw [size] at span
  simpa [Nat.add_assoc] using span

/-- The natural countdown through the full counted span. -/
theorem natural_countdown_counted_fixture (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7)))
          (naturalCountdownHOL n)) (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      CrepSteps.steps (naturalCrepEntry n)
        (crepStateFrom (panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7)))
          (naturalCountdownHOL n)) ≤ 3 + (n+36)*((n+36)*(6*n+8)) := by
  have actual := counted_decl_countdown_simplified n (executableState (naturalCountdownHOL n))
    (exactState (naturalCountdownHOL n)) (source_related _) (source_ranged _) "x" countdown_name_ranged range
    (by change n ≤ 2^64; omega) 0 context primitive handler [] 0
  obtain ⟨result,_,run,_,_,resultEq⟩ := actual
  subst result
  have run' : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL (naturalCountdown n))).structs []
      (executableState (progToHOL (naturalCountdown n))).baseAddress (executableState (progToHOL (naturalCountdown n))).topAddress
      panSemBitVec64BytesInWord (n+3) (executableState (progToHOL (naturalCountdown n))).locals
      (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
      (executableState (progToHOL (naturalCountdown n))).ffi (naturalCountdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (naturalCountdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (naturalCountdown n))).locals "x"))
          (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
          (executableState (progToHOL (naturalCountdown n))).ffi [.word 0],6*n+7) := by
    simpa [naturalCountdownHOL,naturalCountdown] using run
  have span := fixture_counted_span (naturalCountdown n) (naturalCountdown_supported n) context primitive handler (n+3) (6*n+7) (6*n+7)
    (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (naturalCountdown n))).locals "x"))
    (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
    (executableState (progToHOL (naturalCountdown n))).ffi 0 run' (by omega)
  have simpEq : panSimpProg (naturalCountdown n) = naturalCountdown n := by
    simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]
  simp only [simpEq] at span
  have size := natural_compiled_size n range
  change ∃ final, evalCrepSemHOLProgExact
      (crepStateFrom (panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7)))
        (naturalCountdownHOL n)) (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
    CrepSteps.steps (naturalCrepEntry n)
      (crepStateFrom (panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7)))
        (naturalCountdownHOL n)) ≤
    3 + sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) *
      (sizeOf (compileProgExactHOLW (naturalCalleeContext n) (naturalCountdownHOL n)) * (6*n+7+1)) at span
  rw [size] at span
  simpa [Nat.add_assoc] using span

/-- The comparison witness through the full counted span. -/
theorem branching_counted_fixture
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branching (clockedFixtureSource branching 6)) branchingHOL)
        branchCrepEntry = (some (.return [.word 7]),final) ∧
      CrepSteps.steps branchCrepEntry
        (crepStateFrom (panSimpSourceState branching (clockedFixtureSource branching 6)) branchingHOL) ≤ 10111 := by
  have run := branching_run context primitive handler
  have run' : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL branching)).structs []
      (executableState (progToHOL branching)).baseAddress (executableState (progToHOL branching)).topAddress
      panSemBitVec64BytesInWord 2 (executableState (progToHOL branching)).locals
      (executableState (progToHOL branching)).globals (executableState (progToHOL branching)).memory
      (executableState (progToHOL branching)).ffi branching
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL branching)))) =
        some (.returned (executableState (progToHOL branching)).locals (executableState (progToHOL branching)).globals
          (executableState (progToHOL branching)).memory (executableState (progToHOL branching)).ffi [.word 7],6) := by
    simpa only [← branching_hol_eq] using run
  have span := fixture_counted_span branching branching_supported context primitive handler 2 6 6
    (executableState (progToHOL branching)).locals (executableState (progToHOL branching)).globals
    (executableState (progToHOL branching)).memory (executableState (progToHOL branching)).ffi 7 run' (by omega)
  simp only [branching_simp_program,← branching_hol_eq] at span
  have relations := supported_callee_relations branching branching_supported
  simp only [← branching_hol_eq] at relations
  have lookup := relations.1
  have codeEq : compileProgExactHOLW branchCalleeContext branchingHOL = branchCrepBody := by
    rw [branchCrepCode_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf branchCrepBody = 38 := by decide
  change ∃ final,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branching (clockedFixtureSource branching 6)) branchingHOL)
        branchCrepEntry = (some (.return [.word 7]),final) ∧
      CrepSteps.steps branchCrepEntry
        (crepStateFrom (panSimpSourceState branching (clockedFixtureSource branching 6)) branchingHOL) ≤
        3 + sizeOf (compileProgExactHOLW branchCalleeContext branchingHOL) *
          (sizeOf (compileProgExactHOLW branchCalleeContext branchingHOL) * 7) at span
  rw [codeEq,size] at span
  simpa using span

/-- The loop executing both conditional arms through the full counted span. -/
theorem branching_loop_counted_fixture
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop))
        branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      CrepSteps.steps branchingLoopCrepEntry
        (crepStateFrom (panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop)) ≤ 57627 := by
  have run := branchingLoop_source_run context primitive handler
  have span := fixture_counted_span branchingLoop branchingLoop_supported context primitive handler 7 23 23
    (executableState (progToHOL branchingLoop)).locals (executableState (progToHOL branchingLoop)).globals
    (executableState (progToHOL branchingLoop)).memory (executableState (progToHOL branchingLoop)).ffi 7 run (by omega)
  simp only [branchingLoop_simp_program] at span
  have lookup := (supported_callee_relations branchingLoop branchingLoop_supported).1
  have codeEq : compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop) = branchingLoopCrepBody := by
    rw [branchingLoop_code_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf branchingLoopCrepBody = 49 := by decide
  change ∃ final, evalCrepSemHOLProgExact
      (crepStateFrom (panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop))
      branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
    CrepSteps.steps branchingLoopCrepEntry
      (crepStateFrom (panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop)) ≤
        3 + sizeOf (compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop)) *
          (sizeOf (compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop)) * (23+1)) at span
  rw [codeEq,size] at span
  simpa using span

end SteppedFlapjack.Concrete
