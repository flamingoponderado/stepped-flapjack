import SteppedFlapjack.PanToCrepSteps.CountdownZeroFrontendSafe
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs

/-! Carry concrete Word stack safety into the source-return machine bound. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- When the compiler inputs are the actual zero-count optimized Word code,
the source return has a successful machine outcome within the fitting-frame
bound. No resource-limit outcome is needed. -/
theorem FullInitAssignLoopInputs.countdownZero_machineBound_safe {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (target : LoopSemStateFiniteExact 64 σ)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt entry limit target)
    (programShapes : ∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body)
    (entryMember : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
    (sourceFinal : PanSemStateFiniteExact 64 σ)
    (ready : ∀ word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ,
      loopToWordStateRelHOLExact {target with locals := .ln} word →
      ∃ extra, FullInitReturnedReady entry {target with locals := .ln, clock := target.clock+extra}
        {word with clock := word.clock+extra} limit sourceFinal)
    (acEq : native.ac = riscvConfig)
    (wordCode : sptFromAList (compile native.wc riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))).2 = countdownZeroWordCode)
    (entryBody : HolProg 64)
    (zeroEntry : sptLookup firstLoopName native.stack.code = some (.seq (.stackAlloc 0) entryBody))
    (enabled : native.stack.useStack = true) :
    ∃ ticks finalMachine finalFfi,
      ticks ≤ native.backend.successTickLimit native.wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let initial := {target with locals := .ln}
  have data : LoopWordDataRel initial {countdownZeroInitialWord native.stack native.coracle with
      code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))} := by
    simpa only [initial,LoopWordDataRel,acEq,wordCode,countdownZeroInitialWord,countdownZeroLimit] using native.data
  obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordRel,safe,base,wordLocals⟩ :=
    countdownZero_wholeFrontend_safe native.arch native.crepPrograms programShapes native.wc entry
      (assignLoopEntryWordContext entry) (firstLoopName,2) entryMember initial
      (by simpa [initial] using native.loopCode) native.stack native.coracle
      (by simpa only [acEq] using native.codeEq) (by simpa only [acEq] using native.bitmapsPrefix)
      (by simpa only [acEq,countdownZeroLimit] using native.ok) limit data native.backend entryBody zeroEntry enabled wordCode
  obtain ⟨extra,nativeReady⟩ := ready word wordRel
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,success,events⟩ :=
    FullInitReturnedReady.run_shifted_safe (loop := initial) (sourceFinal := sourceFinal) extra nativeReady setup base 0
      (by rfl) (by simpa [assignLoopEntryWordContext] using contextEq) wordLocals safe
  subst outcome
  refine ⟨ticks,finalMachine,finalFfi,?_,?_,events⟩
  · simpa only [tickEq] using bound
  · simpa only [mcEq,labEq,machineEq] using run

end SteppedFlapjack.PanToCrepSteps
