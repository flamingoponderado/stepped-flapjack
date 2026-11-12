import SteppedFlapjack.Concrete.GlobalStructCountedMachine
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The named pair source compiles to the bytes run by the initialized machine,
which halts at a numeric clock with the source's I/O events. -/
theorem pairGeneral_namedSource_numeric : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig namedGlobalStructProgram =
      some (fixtureCodeBytes (globalSourceCode globalStructProgram),globalSourceBitmaps globalStructProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode globalStructProgram))) sourceFfi
      304799299979875449948 (configuredMachineState (globalSourceCode globalStructProgram) (globalSourceBitmaps globalStructProgram)) =
        (.halt .success,finalMachine,finalFfi) ∧
    semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram = .terminate .success finalFfi.ioEvents := by
  have safe : fixtureStackSafe (globalSourceCode globalStructProgram) = true := by
    rw [pairSourceCode]
    exact globalStruct_nativeSafe
  have success : (fixtureRemoveLabels (globalSourceCode globalStructProgram)).isSome = true := by
    rw [pairSourceCode]
    exact globalStruct_nativeCompilerFacts.1
  obtain ⟨compilerFinal,compiled⟩ := globalSource_compilerOutputFor namedGlobalStructProgram globalStructProgram
    pairNamed_rawWords safe success
  obtain ⟨machine,ffi,run,semantics⟩ := pairGeneral_namedSource
  refine ⟨compilerFinal,machine,ffi,compiled,?_,semantics⟩
  rw [← pairUnified_clock_numeric]
  exact run

end SteppedFlapjack.Concrete
