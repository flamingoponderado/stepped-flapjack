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
import SteppedFlapjack.StackSteps.AddClock
import SteppedFlapjack.StackToLabSteps
import SteppedFlapjack.StackRemoveSteps.Defs
import SteppedFlapjack.StackRemoveSteps.CopyEachSteps
import SteppedFlapjack.StackRemoveSteps.CopyLoopSteps

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
- `SteppedFlapjack.StackSteps.AddClock`: `steps_addClock`, clock monotonicity
  of the step count — a run that does not time out takes the same number of
  steps at any larger clock, which is what lets a run-clock bound be reused
  when the compiler correctness induction raises a `Seq`'s second clock
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackToLabSteps`: adapted copies of Flapjack's `stack_to_lab`
  `flatten_correct` proof with the LabSem run bounded by `flattenStepFactor`
  ticks per StackSem step, assembled as `flattenCorrectWithin` and lifted to
  the start call as `flattenSemanticsWithin` (stepped-flapjack#2, phase C1);
- `SteppedFlapjack.StackRemoveSteps.Defs`: program-dependent expansion costs for
  the `stack_remove` pass, including `leafCost` and the step-count bounds for
  the `upshift`, `downshift` and `stackFree` expansions
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CopyEachSteps`: the per-bitmap-word copy
  loop's fine-grained step bound `15 * (pattern.toNat + 1) + 3`, carried by an
  adapted `copyEachThmWithin` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CopyLoopSteps`: the outer bitmap-list copy
  loop's bound `copyLoopSteps width (bitmaps.length - index)`, carried by an
  adapted `copyLoopThmWithin` (stepped-flapjack#2, phase C3, in progress).

Module names moved from `Flapjack.*` to `SteppedFlapjack.*`; declarations keep
their names in the `Flapjack` namespace. The tests are in the separate
`SteppedFlapjackTests` library, rooted at `SteppedFlapjack.Tests`.
-/
