import SteppedFlapjack.PanToCrepSteps.CountdownZeroMachineSafe
import SteppedFlapjack.LoopToWordSteps.ExplicitTickLimit

/-! Explicit compiler-data bound for the zero-count machine run. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- A successful zero-count run bounded by a calculation on compiler data. -/
theorem FullInitAssignLoopInputs.countdownZero_machineBound_explicit {σ : Type}
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
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (startEq : start = ofString "main") (archEq : native.arch = riscvConfig.isa)
    (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    ∃ ticks finalMachine finalFfi,
      ticks ≤ explicitTickLimit native.backend.dataConf native.backend.maxHeap native.backend.sp native.backend.offset
        native.backend.bitmaps native.backend.inputCode native.backend.coracle native.backend.labCode native.backend.lab.codeBuffer
        native.wc riscvConfig (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  obtain ⟨ticks,finalMachine,finalFfi,bound,run,events⟩ :=
    native.countdownZero_machineBound_safe declarations start caller loopCtxt entry limit target programShapes entryMember
      sourceFinal ready acEq declarationsEq startEq archEq wcEq
  exact ⟨ticks,finalMachine,finalFfi,bound.trans (native.backend.successTickLimit_le_explicit
    native.wc riscvConfig (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
    entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit),run,events⟩

end SteppedFlapjack.PanToCrepSteps
