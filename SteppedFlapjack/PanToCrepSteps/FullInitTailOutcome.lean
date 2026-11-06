import SteppedFlapjack.LoopToWordSteps.FullInitTailSetup
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry

/-! Source return outcomes through the full initialization route. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- A returned Pancake word produces a successful RISC-V outcome with the
same final events, unless native execution reports a resource limit. -/
theorem returned_fullInitTail_outcome {F : Type}
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (sourceFinal panPost : PanSemStateFiniteExact 64 F) (crepPost : CrepSemHOLState 64 F)
    (loopSource loopPost : LoopSemStateFiniteExact 64 F) (crepResult : Option (CrepResultHOLExact 64))
    (returned : BitVec 64)
    (globalRel : panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal panPost)
    (panCrepRel : panToCrepStateRelFiniteExact panPost crepPost)
    (resultRel : pcCompileCorrectResultRel ctxt panPost crepPost (some (.returned (.val (.word returned)))) crepResult)
    (crepLoopRel : crepToLoopStateRelExact crepPost loopPost)
    (p : HolLoopProg 64) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (ready : FullInitTailReady p loopSource loopPost (resultToLoop crepResult) word limit)
    (setup : FullInitTailSetup p word limit)
    (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat)
    (sourceEmpty : loopSource.locals = .ln)
    (contextEq : setup.ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln)
    (wordLocals : word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents)) := by
  have globalFfi : sourceFinal.ffi = panPost.ffi := by
    rcases globalRel with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,ffi,_⟩
    exact ffi
  have panFfi : panPost.ffi = crepPost.ffi := panCrepRel.2.2.2.2.2.2.2.1
  have loopFfi : crepPost.ffi = loopPost.ffi := crepLoopRel.2.2.2.2.1
  have traceEq : sourceFinal.ffi.ioEvents = loopPost.ffi.ioEvents := by rw [globalFfi,panFfi,loopFfi]
  have resultEq : crepResult = some (.return (flattenHOL (.val (.word returned)))) := by
    simpa only [pcCompileCorrectResultRel] using resultRel
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,correspondence⟩ :=
    ready.run_native setup base frameSize sourceEmpty contextEq wordLocals
  refine ⟨outcome,ticks,finalMachine,finalFfi,bound,run,?_⟩
  rcases correspondence with ⟨matched,events⟩ | ⟨resource,events⟩
  · rw [resultEq] at matched
    cases matched
    exact Or.inl ⟨rfl,by simpa only [traceEq] using events⟩
  · exact Or.inr ⟨resource,by simpa only [traceEq] using events⟩

/-- A full-initialization outcome stated against the original source's final trace. -/
def FullInitReturnedReady {F : Type} (p : HolLoopProg 64)
    (loopSource : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (limit : Nat) (sourceFinal : PanSemStateFiniteExact 64 F) : Prop :=
  ∀ (setup : FullInitTailSetup p word limit)
    (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat),
    loopSource.locals = .ln →
    setup.ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln →
    word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals →
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents))

/-- Relate the generic backend-ready result to a returned Pancake word. -/
theorem fullInitReturnedReady_of_return {F : Type}
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (sourceFinal panPost : PanSemStateFiniteExact 64 F) (crepPost : CrepSemHOLState 64 F)
    (loopSource loopPost : LoopSemStateFiniteExact 64 F) (crepResult : Option (CrepResultHOLExact 64))
    (returned : BitVec 64)
    (globalRel : panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal panPost)
    (panCrepRel : panToCrepStateRelFiniteExact panPost crepPost)
    (resultRel : pcCompileCorrectResultRel ctxt panPost crepPost (some (.returned (.val (.word returned)))) crepResult)
    (crepLoopRel : crepToLoopStateRelExact crepPost loopPost)
    (p : HolLoopProg 64) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (ready : FullInitTailReady p loopSource loopPost (resultToLoop crepResult) word limit) :
    FullInitReturnedReady p loopSource word limit sourceFinal := by
  intro setup base frameSize sourceEmpty contextEq wordLocals
  exact returned_fullInitTail_outcome globals ctxt sourceFinal panPost crepPost loopSource loopPost crepResult returned
    globalRel panCrepRel resultRel crepLoopRel p word limit ready setup base frameSize sourceEmpty contextEq wordLocals

end SteppedFlapjack.PanToCrepSteps
