import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.Concrete.NaturalCountdownSourceLab
import SteppedFlapjack.Concrete.BranchingSourceLab
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-! Concrete successful RISC-V runs for the Phase 6 witness programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps

private def fixtureContext : PanValueFfiContext (RiscV.Word 64) := riscv64PanValueFfiContext (fun _ => false)
private def fixturePrimitive : PanPrimitiveHandler (RiscV.Word 64) := fun _ _ => none
private def fixtureHandler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit := fun _ _ _ _ _ _ _ => none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem comparison_bitmap :
    (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2).1 = [4] := by
  rw [comparison_optimized_table]
  with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem branching_bitmap :
    (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2).1 = [4] := by
  rw [branch_optimized_table]
  with_unfolding_all decide

/-- The original countdown compiler produces the bytes loaded by the machine. -/
theorem countdownFixture_compiler (n : Nat) :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (progToHOL (countdown n))) =
        some (fixtureCodeBytes (countdownNativeStackCode n),[4],final) :=
  fixturePancakeCompiler_output (progToHOL (countdown n)) (countdownWordPrograms n) (countdownNativeStackCode n)
    (countdown_panToWord n) rfl (countdown_native_bitmaps n) (countdown_stackSafe n) (countdown_compiler_facts n).1

/-- The original natural countdown compiler produces the same loaded bytes. -/
theorem naturalCountdownFixture_compiler (n : Nat) :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (progToHOL (naturalCountdown n))) =
        some (fixtureCodeBytes (countdownNativeStackCode n),[4],final) :=
  fixturePancakeCompiler_output (progToHOL (naturalCountdown n)) (countdownWordPrograms n) (countdownNativeStackCode n)
    (naturalCountdown_panToWord n) rfl (countdown_native_bitmaps n) (countdown_stackSafe n) (countdown_compiler_facts n).1

/-- The original comparison compiler produces the bytes loaded by the machine. -/
theorem comparisonFixture_compiler :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (progToHOL branching)) =
        some (fixtureCodeBytes comparisonNativeCode,[4],final) :=
  fixturePancakeCompiler_output (progToHOL branching) comparisonWordPrograms comparisonNativeCode
    comparison_panToWord rfl comparison_bitmap comparison_stackSafe comparison_compiler_facts.1

/-- The original branching-loop compiler produces the bytes loaded by the machine. -/
theorem branchingLoopFixture_compiler :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (progToHOL branchingLoop)) =
        some (fixtureCodeBytes branchingLoopNativeCode,[4],final) :=
  fixturePancakeCompiler_output (progToHOL branchingLoop) branchWordPrograms branchingLoopNativeCode
    branchingLoop_panToWord rfl branching_bitmap branching_stackSafe branching_compiler_facts.1

/-- Concrete full initializer context for every countdown input. -/
noncomputable def countdownFixture_machineContext (n : Nat) :
    FullInitMachineContext (fixtureStack (countdownNativeStackCode n)
      (fixtureCompilerConfig (countdownNativeStackCode n))) :=
  fixtureMachineContext (countdownNativeStackCode n) (fixtureCompilerConfig (countdownNativeStackCode n))
    (fixtureCompiled (countdownNativeStackCode n)).1 (fixtureCompiled (countdownNativeStackCode n)).2
    (countdown_nativeGoodCode n) (fixtureRemoveLabels_eq _ (countdown_compiler_facts n).1)
    (fixtureMachine_allGuards _ (countdown_labGoodCode n _) (countdown_stackSafe n) (countdown_compiler_facts n))

/-- Concrete full initializer context for the comparison witness. -/
noncomputable def comparisonFixture_machineContext :
    FullInitMachineContext (fixtureStack comparisonNativeCode (fixtureCompilerConfig comparisonNativeCode)) :=
  fixtureMachineContext comparisonNativeCode (fixtureCompilerConfig comparisonNativeCode)
    (fixtureCompiled comparisonNativeCode).1 (fixtureCompiled comparisonNativeCode).2
    comparison_nativeGoodCode (fixtureRemoveLabels_eq _ comparison_compiler_facts.1)
    (fixtureMachine_allGuards _ (comparison_labGoodCode _) comparison_stackSafe comparison_compiler_facts)

/-- Concrete full initializer context for the branching-loop witness. -/
noncomputable def branchingLoopFixture_machineContext :
    FullInitMachineContext (fixtureStack branchingLoopNativeCode (fixtureCompilerConfig branchingLoopNativeCode)) :=
  fixtureMachineContext branchingLoopNativeCode (fixtureCompilerConfig branchingLoopNativeCode)
    (fixtureCompiled branchingLoopNativeCode).1 (fixtureCompiled branchingLoopNativeCode).2
    branchingLoop_nativeGoodCode (fixtureRemoveLabels_eq _ branching_compiler_facts.1)
    (fixtureMachine_allGuards _ (branching_labGoodCode _) branching_stackSafe branching_compiler_facts)

/-- The compiled countdown halts successfully on its code-loaded RISC-V
machine at the explicit bound calculated from the source clock `6*n+9`. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600 * (6*n+9) + 1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) := by
  let code := countdownNativeStackCode n
  let cfg := fixtureCompilerConfig code
  let machine := fixtureMachineState code
  obtain ⟨_,_,labPost,_,_,labRun,_⟩ := countdownFixture_source_lab n range cfg machine
    fixtureContext fixturePrimitive fixtureHandler
  have facts := countdown_compiler_facts n
  obtain ⟨machinePost,run⟩ := fixtureLabMachineReturn code (countdown_labGoodCode n cfg)
    (countdown_stackSafe n) facts (1060776773971200*n + 3270750953752551) labPost labRun
  refine ⟨machinePost,labPost.ffi,?_⟩
  have clock : 948 * (1060776773971200*n + 3270750953752551) =
      167602730287449600 * (6*n+9) + 1592247331570371948 := by omega
  rw [← clock]
  exact run

/-- The natural countdown compiles to the same code and has the same
explicit successful machine run. -/
theorem naturalCountdownFixture_machine (n : Nat) (range : n < 2^64) :
    panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
      (progToHOL (naturalCountdown n))) = countdownWordPrograms n ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600 * (6*n+9) + 1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) :=
  ⟨naturalCountdown_panToWord n,countdownFixture_machine n range⟩

/-- The compiled comparison witness halts successfully at a closed clock. -/
theorem comparisonFixture_machine :
    ∃ machinePost ffiPost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart comparisonNativeCode)) sourceFfi
      90715439766875148 (fixtureMachineState comparisonNativeCode) = (.halt .success,machinePost,ffiPost) := by
  let cfg := fixtureCompilerConfig comparisonNativeCode
  let machine := fixtureMachineState comparisonNativeCode
  obtain ⟨_,_,labPost,_,_,labRun,_⟩ := comparisonFixture_source_lab cfg machine fixtureContext fixturePrimitive fixtureHandler
  obtain ⟨machinePost,run⟩ := fixtureLabMachineReturn comparisonNativeCode (comparison_labGoodCode cfg)
    comparison_stackSafe comparison_compiler_facts 95691392159151 labPost labRun
  exact ⟨machinePost,labPost.ffi,by simpa using run⟩

/-- The compiled branching-loop witness halts successfully at a closed clock. -/
theorem branchingLoopFixture_machine :
    ∃ machinePost ffiPost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart branchingLoopNativeCode)) sourceFfi
      36771214184170446348 (fixtureMachineState branchingLoopNativeCode) = (.halt .success,machinePost,ffiPost) := by
  let cfg := fixtureCompilerConfig branchingLoopNativeCode
  let machine := fixtureMachineState branchingLoopNativeCode
  obtain ⟨_,_,labPost,_,_,labRun,_⟩ := branchingLoopFixture_source_lab cfg machine fixtureContext fixturePrimitive fixtureHandler
  obtain ⟨machinePost,run⟩ := fixtureLabMachineReturn branchingLoopNativeCode (branching_labGoodCode cfg)
    branching_stackSafe branching_compiler_facts 38788200616213551 labPost labRun
  exact ⟨machinePost,labPost.ffi,by simpa using run⟩

end SteppedFlapjack.Concrete
