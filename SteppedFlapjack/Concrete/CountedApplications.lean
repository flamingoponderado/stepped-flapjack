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

/-- The clocked fixture satisfies the source relation and scalar-local
premises uniformly for any supported source body. -/
theorem clockedFixture_premises (program : Prog (RiscV.Word 64)) (n : Nat) :
    PanSemStateRelExec (clockedFixtureProduction program n) (clockedFixtureSource program n).toExact ∧
    PanSemStateRelExecRanged (clockedFixtureProduction program n) ∧
    WordLocals (clockedFixtureProduction program n).locals := by
  constructor
  · obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL program)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  constructor
  · exact PanSemStateRelExecRanged.setClock (source_ranged (progToHOL program)) n
  · intro name value found
    simp [clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found

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
        3 + CrepSteps.statementWeight (compileProgExactHOLW callee body) * (n + 1 + CrepSteps.statementWeight (compileProgExactHOLW callee body)) ∧
      FfiStateRel postFfi final.ffi := by
  let source := clockedFixtureSource program n
  let production := clockedFixtureProduction program n
  let _ : DecidablePred source.memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  obtain ⟨rel,ranged,words⟩ := clockedFixture_premises program n
  have run' : evalPanValueFfiProgSteps context primitive handler production.structs [] production.baseAddress
      production.topAddress panSemBitVec64BytesInWord fuel production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count) := by
    simpa [production,clockedFixtureProduction,panSemBitVec64MemoryAccess] using run
  exact supported_counted_full_frontend program supported production source rel ranged words rfl rfl rfl rfl
    context primitive handler [] fuel count n postLocals postGlobals postMemory postFfi word run' budget rfl

end SteppedFlapjack.Concrete
