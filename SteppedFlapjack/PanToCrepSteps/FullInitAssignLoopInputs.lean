import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopNative
import SteppedFlapjack.PanToCrepSteps.FullInitTailClockOutcome
import SteppedFlapjack.CrepToLoopSteps.FullInitNativeFrontend

/-! Compiler-derived full-initialization bounds for source entries. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps SteppedFlapjack.WordToStackSteps

/-- The compiled assignment-loop entry fits in the initial Stack space. -/
def assignLoopFrameFits {F : Type} (arch : AsmArchitecture)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (entry : HolLoopProg 64) (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  nativeEntryFrameSize (ac.regCount-(5+ac.avoidRegs.length))
    (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1),
        entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) firstLoopName)).2.2 ≤ stack.stackSpace

/-- Shared actual compiler inputs with the full initialization machine context. -/
structure FullInitAssignLoopInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F)
    extends AssignLoopCompilerInputs declarations start caller loopCtxt entry limit loop where
  backend : FullInitMachineContext stack
  frameFits : assignLoopFrameFits arch crepPrograms wc ac entry stack

/-- A proved source return yields a full-initialization tick bound. -/
theorem FullInitAssignLoopInputs.machineBound {σ : Type}
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
        {word with clock := word.clock+extra} limit sourceFinal) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ (native.backend.successTickLimit native.wc native.ac
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents)) := by
  let initial := {target with locals := .ln}
  obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordRel,base,frameSize,wordLocals⟩ :=
    wholeFullInitTail_frontend_setup native.arch native.crepPrograms programShapes
      native.wc native.ac entry (assignLoopEntryWordContext entry) (firstLoopName,2) entryMember
      initial (by simpa [initial] using native.loopCode) native.stack native.coracle native.codeEq native.bitmapsPrefix native.ok limit
      (by simpa [initial,LoopWordDataRel] using native.data) native.backend native.frameFits
  obtain ⟨extra,nativeReady⟩ := ready word wordRel
  obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,correspondence⟩ :=
    FullInitReturnedReady.run_shifted (loop := initial) (sourceFinal := sourceFinal) extra nativeReady setup base frameSize (by rfl) (by simpa [assignLoopEntryWordContext] using contextEq) wordLocals
  refine ⟨outcome,ticks,finalMachine,finalFfi,?_,?_,?_⟩
  · rw [tickEq] at bound
    exact bound
  · simpa only [mcEq,labEq,machineEq] using run
  · rcases correspondence with success | ⟨resource,events⟩
    · exact Or.inl success
    · exact Or.inr ⟨resource,events⟩


end SteppedFlapjack.PanToCrepSteps
