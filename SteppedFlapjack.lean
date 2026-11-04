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
  composition across passes, and machine step counts (stepped-flapjack#2).

Module names moved from `Flapjack.*` to `SteppedFlapjack.*`; declarations keep
their names in the `Flapjack` namespace. The tests are in the separate
`SteppedFlapjackTests` library, rooted at `SteppedFlapjack.Tests`.
-/
