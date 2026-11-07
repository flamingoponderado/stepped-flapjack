import SteppedFlapjack.PanToCrepSteps.FullInitTailOutcome
import SteppedFlapjack.LoopToWordSteps.FullInitTailClock

/-! Use the native entry setup after the Loop simulation's clock shift. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- A backend setup built for the original Word state applies to the shifted
Loop/Word execution without changing the native machine or tick bound. -/
theorem FullInitReturnedReady.run_shifted {F : Type} {p : HolLoopProg 64}
    {loop : LoopSemStateFiniteExact 64 F} {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    {limit : Nat} {sourceFinal : PanSemStateFiniteExact 64 F} (extra : Nat)
    (ready : FullInitReturnedReady p {loop with clock := loop.clock+extra}
      {word with clock := word.clock+extra} limit sourceFinal)
    (setup : FullInitTailSetup p word limit)
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
    ready.1 (setup.withWordClock (word.clock+extra)) base frameSize sourceEmpty contextEq wordLocals
  refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,correspondence⟩
  simpa only [FullInitTailSetup.withWordClock_tickLimit] using bound

/-- A stack-safe setup keeps the successful result after the clock shift. -/
theorem FullInitReturnedReady.run_shifted_safe {F : Type} {p : HolLoopProg 64}
    {loop : LoopSemStateFiniteExact 64 F} {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F}
    {limit : Nat} {sourceFinal : PanSemStateFiniteExact 64 F} (extra : Nat)
    (ready : FullInitReturnedReady p {loop with clock := loop.clock+extra}
      {word with clock := word.clock+extra} limit sourceFinal)
    (setup : FullInitTailSetup p word limit)
    (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat)
    (sourceEmpty : loop.locals = .ln)
    (contextEq : setup.ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln)
    (wordLocals : word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals)
    (safe : setup.wordSafe) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,success,events⟩ :=
    ready.2 (setup.withWordClock (word.clock+extra)) base frameSize sourceEmpty contextEq wordLocals
      ((FullInitTailSetup.withWordClock_wordSafe setup _).2 safe)
  refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,success,events⟩
  simpa only [FullInitTailSetup.withWordClock_tickLimit] using bound

end SteppedFlapjack.PanToCrepSteps
