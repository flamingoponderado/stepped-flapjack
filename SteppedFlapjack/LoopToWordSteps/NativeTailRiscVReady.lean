import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup
import SteppedFlapjack.WordToStackSteps.TailEntryFrame

/-! Loop/Word local initialization for a native tail entry. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LabToTargetSteps SteppedFlapjack.WordToStackSteps

/-- For an empty Loop entry and the compiler-selected zero-argument context,
the native call environment supplies all Loop/Word local premises. -/
theorem TailRiscVReady.run_native {F : Type} {p : HolLoopProg 64}
    {source sourcePost : LoopSemStateFiniteExact 64 F} {result : Option (LoopResultExact 64)}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (ready : TailRiscVReady p source sourcePost result word limit)
    (setup : TailRiscVSetup p word limit)
    (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat)
    (sourceEmpty : source.locals = .ln)
    (contextEq : setup.ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln)
    (wordLocals : word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  have localFacts := nativeTailEntry_loopLocals p base frameSize
  have lookup := (nativeEntry_locals base frameSize 0).2.2
  apply ready setup
  · simpa only [sourceEmpty,contextEq,wordLocals] using localFacts.1
  · simpa only [wordLocals] using lookup
  · simpa only [contextEq] using localFacts.2

end SteppedFlapjack.LoopToWordSteps
