import SteppedFlapjack.Concrete.FixtureMachineGuards
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-! Concrete successful RISC-V runs for the Phase 6 witness programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

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

end SteppedFlapjack.Concrete
