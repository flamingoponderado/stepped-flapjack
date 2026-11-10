import SteppedFlapjack.Concrete.Phase7Word
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.FixtureMachineGuards

/-! Supported programs in the actual initialized native backend. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

def supportedWordPrograms (program : Prog (RiscV.Word 64)) :=
  loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL (panSimpProg program))))

def supportedAllocated (program : Prog (RiscV.Word 64)) :=
  Flapjack.Compiler.Backend.WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (supportedWordPrograms program)

def supportedNative (program : Prog (RiscV.Word 64)) :=
  WordToStack.Native.compileNative riscvConfig false (supportedAllocated program).2

set_option maxHeartbeats 1000000 in
/-- Counted source execution reaches the Word state initialized from the
actual native Stack program, with a code-derived Word visit bound. -/
theorem supported_counted_initializedWord
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
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
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (countBound : count ≤ n)
    (cfg : LabToTarget.Config) (frame : Nat)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 (supportedNative program).2.2.2)
    (frameLookup : sptLookup 64 (fixtureWord (supportedNative program).2.2.2
      (supportedAllocated program).2 cfg).stackSize = some frame) :
    let code := (supportedNative program).2.2.2
    let words := (supportedAllocated program).2
    let state := {(fixtureWord code words cfg) with clock := 6*supportedLoopVisits program n+1}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact
        (crepStateFrom (panSimpSourceState program (clockedFixtureSource program (n+1))) (progToHOL (panSimpProg program)))
        (.seq .skip (.call none (entryName (progToHOL (panSimpProg program))) [])) =
        (some (.return [.word word]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word word]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤ supportedWordBound program n ∧
      FfiStateRel postFfi final.ffi := by
  let body := progToHOL (panSimpProg program)
  let creps := crepPrograms body
  let words := (supportedAllocated program).2
  let code := (supportedNative program).2.2.2
  let starter := fixtureWord code words cfg
  have alloc : (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (supportedWordPrograms program)).2 = words := by
    simp only [words,supportedAllocated,phase3WordConfig_eq]
    have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    rw [Flapjack.Compiler.Backend.WordToWord.compileWith_eq_compile _ allocator]
  have memoryRel := fixtureCrep_memory program (n+1) body code cfg good
  obtain ⟨final,post,crepRun,stateRel,result,ffi,bound,crepFfi⟩ := supported_counted_word program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound
    (fixtureStack code cfg).memory memoryRel starter frame
  have startEq := fixtureStarter program (n+1) (supportedLoopBudget program n) body creps code words cfg good frame
    (6*supportedLoopVisits program n+1) frameLookup
  let pan := panSimpSourceState program (clockedFixtureSource program (n+1))
  let crep := crepStateFrom pan body
  let timed := {crep with clock := crep.clock + supportedLoopBudget program n}
  let wordState := {(phase3Starter riscvConfig.isa timed creps starter fixtureHeapLength 64 frame) with
    memory := (fixtureStack code cfg).memory, clock := 6*supportedLoopVisits program n+1,
    code := sptFromAList words}
  have startEq' : wordState = {starter with clock := 6*supportedLoopVisits program n+1} := by
    exact startEq
  have alloc' : (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL (panSimpProg program)))))).2 = words := alloc
  simp only [alloc'] at result ffi bound
  change (WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) wordState).1 = _ at result
  change (WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) wordState).2.ffi = _ at ffi
  change WordSteps.steps (.call none (some 64) [0] none) wordState ≤ _ at bound
  rw [startEq'] at result ffi bound
  exact ⟨final,post,crepRun,stateRel,result,ffi,bound,crepFfi⟩
end SteppedFlapjack.Concrete
