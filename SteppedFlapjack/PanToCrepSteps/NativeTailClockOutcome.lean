import SteppedFlapjack.PanToCrepSteps.NativeTailOutcome
import SteppedFlapjack.LoopToWordSteps.TailRiscVClock

/-! Use the native entry setup after the Loop simulation's clock shift. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- A backend setup built for the original Word state applies to the shifted
Loop/Word execution without changing the native machine or tick bound. -/
theorem NativeReturnedReady.run_shifted {F : Type} {p : HolLoopProg 64}
    {loop : LoopSemStateFiniteExact 64 F} {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    {limit : Nat} {sourceFinal : PanSemStateFiniteExact 64 F} (extra : Nat)
    (ready : NativeReturnedReady p {loop with clock := loop.clock+extra}
      {word with clock := word.clock+extra} limit sourceFinal)
    (setup : TailRiscVSetup p word limit)
    (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat)
    (sourceEmpty : loop.locals = .ln)
    (contextEq : setup.ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln)
    (wordLocals : word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents)) := by
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,correspondence⟩ :=
    ready (setup.withWordClock (word.clock+extra)) base frameSize sourceEmpty contextEq wordLocals
  refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,correspondence⟩
  simpa only [TailRiscVSetup.withWordClock_tickLimit] using bound

end SteppedFlapjack.PanToCrepSteps
