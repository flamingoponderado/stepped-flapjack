import SteppedFlapjack.Concrete.Phase7SourceBehaviour

/-! Explicit source-to-RISC-V composition for supported programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps

set_option maxHeartbeats 1000000 in
/-- A supported counted source return reaches a successfully halting RISC-V
machine at a code-derived clock, with matching source and machine observable events. -/
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
    (calleeFits : supportedCalleeFrame program ≤
      (fixtureStack (supportedNative program).2.2.2 (fixtureCompilerConfig (supportedNative program).2.2.2)).stack.length)
    (safe : fixtureStackSafe (supportedNative program).2.2.2 = true)
    (facts : (fixtureRemoveLabels (supportedNative program).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length % 4 = 0) :
    let code := (supportedNative program).2.2.2
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL program)) = some (fixtureCodeBytes code,[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
      (supportedMachineFactor program * n + supportedMachineOffset program) (fixtureMachineState code) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel postFfi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL program)) = .terminate .success ffiPost.ioEvents := by
  let code := (supportedNative program).2.2.2
  let cfg := fixtureCompilerConfig code
  have good := supported_nativeGoodCode program supported
  have labGood := supported_labGoodCode program supported
  obtain ⟨compilerFinal,compiled⟩ := supported_compiler_output program supported safe facts.1
  obtain ⟨stackPost,stackRun,stackBound,stackFfi⟩ := supported_counted_nativeStack program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound
    cfg good calleeFits
  obtain ⟨labPost,labRun,labFfi⟩ := fixtureStack_lab_return code cfg (fixtureMachineState code) good
    (supportedWordBound program n+1) (supportedStackBound program n) stackPost stackRun stackBound
  obtain ⟨machinePost,machineRun⟩ := fixtureLabMachineReturn code labGood safe facts
    (fixtureLabTickLimit code cfg (supportedStackBound program n)) labPost labRun
  obtain ⟨events,semantics,sourceEvents⟩ := supported_counted_semantics program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound
  have machineEvents : FfiEventListRel postFfi.ioEvents labPost.ffi.ioEvents := by
    simpa [labFfi] using stackFfi.2.1
  have sameEvents := ffiEventListRel_unique postFfi.ioEvents events labPost.ffi.ioEvents sourceEvents machineEvents
  refine ⟨compilerFinal,compiled,machinePost,labPost.ffi,?_,machineEvents,?_⟩
  · rw [← supportedMachineTicks_affine]
    exact machineRun
  · simpa only [sameEvents] using semantics
end SteppedFlapjack.Concrete
