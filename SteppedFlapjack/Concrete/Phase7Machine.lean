import SteppedFlapjack.Concrete.Phase7Stack
import SteppedFlapjack.Concrete.FixtureStackLab

/-! Explicit source-to-RISC-V composition for supported programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps

/-- Machine ticks calculated from the source budget and generated code. -/
noncomputable def supportedMachineTicks (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let code := (supportedNative program).2.2.2
  948 * fixtureLabTickLimit code (fixtureCompilerConfig code) (supportedStackBound program n)

set_option maxHeartbeats 1000000 in
/-- A supported counted source return reaches a successfully halting RISC-V
machine at a code-derived clock, with the source FFI state related to the
machine's final FFI state. -/
theorem supported_counted_machine
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
    (compilerFinal : Backend.Config)
    (compiled : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL program)) = some (fixtureCodeBytes (supportedNative program).2.2.2,[4],compilerFinal))
    (good : StackToLab.Proofs.GoodCode.goodCode 24 (supportedNative program).2.2.2)
    (bitmap : (supportedNative program).1 = [4])
    (calleeFits : ∀ arity callee,
      sptLookup 65 (sptFromAList (supportedAllocated program).2) = some (arity,callee) →
      1 + (compileProgNative riscvConfig false callee arity (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 ≤
        (fixtureStack (supportedNative program).2.2.2 (fixtureCompilerConfig (supportedNative program).2.2.2)).stack.length)
    (labGood : goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab (supportedNative program).2.2.2
        (fixtureCompilerConfig (supportedNative program).2.2.2)).code))
    (safe : fixtureStackSafe (supportedNative program).2.2.2 = true)
    (facts : (fixtureRemoveLabels (supportedNative program).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length % 4 = 0) :
    let code := (supportedNative program).2.2.2
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL program)) = some (fixtureCodeBytes code,[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
      (supportedMachineTicks program n) (fixtureMachineState code) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel postFfi.ioEvents ffiPost.ioEvents := by
  let code := (supportedNative program).2.2.2
  let cfg := fixtureCompilerConfig code
  obtain ⟨stackPost,stackRun,stackBound,stackFfi⟩ := supported_counted_nativeStack program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound
    cfg good bitmap calleeFits
  obtain ⟨labPost,labRun,labFfi⟩ := fixtureStack_lab_return code cfg (fixtureMachineState code) good
    (supportedWordBound program n+1) (supportedStackBound program n) stackPost stackRun stackBound
  obtain ⟨machinePost,machineRun⟩ := fixtureLabMachineReturn code labGood safe facts
    (fixtureLabTickLimit code cfg (supportedStackBound program n)) labPost labRun
  refine ⟨compiled,machinePost,labPost.ffi,machineRun,?_⟩
  simpa [labFfi] using stackFfi.2.1
end SteppedFlapjack.Concrete
