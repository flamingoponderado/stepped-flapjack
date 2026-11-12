import SteppedFlapjack.Concrete.GlobalStructConfiguredWord
import SteppedFlapjack.Concrete.GlobalNamedStruct
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem sourceGood : pancakeGoodCodeHOL globalStructProgram = true := by
  with_unfolding_all decide
theorem globalStruct_actualMachine :
    let code := globalStructNativeCode
    let bs := globalStructNativeBitmaps
    let words := globalStructOptimizedWords
    let limit := globalStructActualOptimizedLimit
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  let cfg := fixtureCompilerConfig globalStructNativeCode
  let word := {(configuredWord globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps) with
    clock := 6*globalStructActualOptimizedLimit+1}
  let call : WordLangProgHOL (BitVec 64) := .call none (some 64) [0] none
  let wordPost := (WordSemStateFiniteExact.evaluate call word).2
  have run : WordSemStateFiniteExact.evaluate call word = (some (.result (.loc 1 0) [.word 8]),wordPost) := by
    apply Prod.ext
    · exact (globalStruct_configuredWordRun cfg).1
    · rfl
  have entry : (64,1,(LoopToWord.compHOL globalStructActualWordContext globalStructActualOptimizedLoop (64,2)).1) ∈
      globalStructActualWordPrograms := by
    simpa [firstLoopName] using globalStruct_actualWordEntry
  have fits : 0xa0020018 + globalStructNativeBitmaps.length*8 ≤ 0xa0410000 := by
    change 0xa0020018 + (compileNative riscvConfig false globalStructOptimizedWords).1.length*8 ≤ 0xa0410000
    rw [globalStruct_nativeBitmap]
    decide
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := generated_initialized_machine
    globalStructCallPrograms _ entry globalStructProgram globalStruct_sourceUnique globalStruct_rawWords
    globalStructActualOptimizedLimit 8 sourceGood fits globalStruct_nativeSafe globalStruct_nativeCompilerFacts
    globalStruct_nativeCapacity wordPost run
  have wordFfi : wordPost.ffi = sourceFfi := (globalStruct_configuredWordRun cfg).2
  exact ⟨finalMachine,finalFfi,machineRun,by simpa [wordFfi] using events⟩

/-- The native witness uses the actual Word compilation of the named source. -/
theorem namedGlobalStruct_rawWords :
    panToWordCompileProgHOL riscvConfig.isa namedGlobalStructProgram = globalStructActualWordPrograms := by
  unfold panToWordCompileProgHOL globalStructActualWordPrograms globalStructCallPrograms
  dsimp only
  rw [namedGlobalStruct_pipeline]

/-- The named-struct source and its actual RISC-V compilation terminate with
    the same I/O events at an explicit bound derived from the generated code. -/
theorem namedGlobalStruct_source_machine :
    let code := globalStructNativeCode
    let bs := globalStructNativeBitmaps
    let words := globalStructOptimizedWords
    let limit := globalStructActualOptimizedLimit
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧
      semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram =
        .terminate .success finalFfi.ioEvents := by
  obtain ⟨machine,ffi,run,events⟩ := globalStruct_actualMachine
  refine ⟨machine,ffi,run,?_⟩
  rw [events]
  exact namedGlobalStruct_semantics

end SteppedFlapjack.Concrete
