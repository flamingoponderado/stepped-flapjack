import SteppedFlapjack.PanValueExpCounted
import SteppedFlapjack.PanExpressionEvaluator
import SteppedFlapjack.PanSteppedSemantics
import SteppedFlapjack.PanValueFfiSemantics
import SteppedFlapjack.PanValueFfiFuel
import SteppedFlapjack.PanValueFfiEventMonotonicity
import SteppedFlapjack.PanValueFfiClockProjection
import SteppedFlapjack.PanValueFfiClockStepsBridge
import SteppedFlapjack.PanCost
import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge
import SteppedFlapjack.StepPreservation.Basic
import SteppedFlapjack.RiscVSteps
import SteppedFlapjack.LabToTargetSteps
import SteppedFlapjack.StackSteps.Defs
import SteppedFlapjack.StackToLabSteps
import SteppedFlapjack.StackRemoveSteps.Defs

/-!
# stepped-flapjack

The step-counted structured Pancake source semantics, split out of Flapjack in
phase 4 of flapjack#1251:

- `SteppedFlapjack.PanValueExpCounted`, `SteppedFlapjack.PanExpressionEvaluator`:
  expression evaluators that count steps;
- `SteppedFlapjack.PanSteppedSemantics`, `SteppedFlapjack.PanValueFfiSemantics`:
  the stepped statement evaluators, including `evalPanValueFfiProgSteps`;
- `SteppedFlapjack.PanValueFfiFuel`, `SteppedFlapjack.PanValueFfiEventMonotonicity`:
  fuel and I/O-event monotonicity of the stepped evaluator;
- `SteppedFlapjack.PanValueFfiClockProjection`,
  `SteppedFlapjack.PanValueFfiClockStepsBridge`: the bridge from Flapjack's
  clocked evaluator to stepped results, which cannot cover timed-out runs;
- `SteppedFlapjack.PanCost`: source-level step costs;
- `SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge`: the
  counted expression evaluator against `PanSem.evalExecuted`;
- `SteppedFlapjack.StepPreservation.Basic`: linear step bounds, their
  composition across passes, and machine step counts (stepped-flapjack#2);
- `SteppedFlapjack.RiscVSteps`: adapted copies of Flapjack's RISC-V encoder
  correctness cases with each step count bounded, assembled as
  `riscv_encoder_correct_within` (stepped-flapjack#2, phase A);
- `SteppedFlapjack.LabToTargetSteps`: adapted copies of Flapjack's
  `lab_to_target` `compile_correct` proof with the target run bounded by
  `labTickBound` ticks per source clock tick, assembled as
  `compileCorrectWithin` and specialised to RISC-V as
  `compileCorrectWithin_riscv` (stepped-flapjack#2, phase B);
- `SteppedFlapjack.StackSteps.Defs`: `steps`, a fine-grained step count of a
  StackSem run, counting every `evaluate` invocation (stepped-flapjack#2,
  phase C);
- `SteppedFlapjack.StackToLabSteps`: adapted copies of Flapjack's `stack_to_lab`
  `flatten_correct` proof with the LabSem run bounded by `flattenStepFactor`
  ticks per StackSem step, assembled as `flattenCorrectWithin` and lifted to
  the start call as `flattenSemanticsWithin` (stepped-flapjack#2, phase C1);
- `SteppedFlapjack.StackRemoveSteps.Defs`: program-dependent expansion costs for
  the `stack_remove` pass, including `leafCost` and the step-count bounds for
  the `upshift`, `downshift` and `stackFree` expansions
  (stepped-flapjack#2, phase C3, in progress).

Module names moved from `Flapjack.*` to `SteppedFlapjack.*`; declarations keep
their names in the `Flapjack` namespace. The tests are in the separate
`SteppedFlapjackTests` library, rooted at `SteppedFlapjack.Tests`.
-/
