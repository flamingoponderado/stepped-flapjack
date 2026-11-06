import SteppedFlapjack.LoopToWordSteps.NativeTailRiscVReady
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopEntry

/-! Source return outcomes and traces at the native RISC-V entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- A returned Pancake word produces a successful RISC-V outcome with the
same final events, unless native execution reports a resource limit. -/
theorem returned_nativeTail_outcome {F : Type}
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64)
    (sourceFinal panPost : PanSemStateFiniteExact 64 F) (crepPost : CrepSemHOLState 64 F)
    (loopSource loopPost : LoopSemStateFiniteExact 64 F) (crepResult : Option (CrepResultHOLExact 64))
    (returned : BitVec 64)
    (globalRel : panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal panPost)
    (panCrepRel : panToCrepStateRelFiniteExact panPost crepPost)
    (resultRel : pcCompileCorrectResultRel ctxt panPost crepPost (some (.returned (.val (.word returned)))) crepResult)
    (crepLoopRel : crepToLoopStateRelExact crepPost loopPost)
    (p : HolLoopProg 64) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (ready : TailRiscVReady p loopSource loopPost (resultToLoop crepResult) word limit)
    (setup : TailRiscVSetup p word limit)
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

end SteppedFlapjack.PanToCrepSteps
