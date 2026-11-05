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
import SteppedFlapjack.StackRemoveSteps.LeafCostBounds
import SteppedFlapjack.StackRemoveSteps.LeafSteps
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Statement
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Seq
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Ite
import SteppedFlapjack.StackRemoveSteps.CompCorrect.Loop
import SteppedFlapjack.StackRemoveSteps.CompCorrect.JumpLower
import SteppedFlapjack.StackRemoveSteps.CompCorrect.RawCall
import SteppedFlapjack.StackRemoveSteps.CallCostBounds
import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallTail
import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnNone

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
- `SteppedFlapjack.StackRemoveSteps.LeafCostBounds`: `leafCost` is at least one
  and dominates every subprogram's factor, which is what lets the `stack_remove`
  correctness induction thread one program-dependent factor down the tree
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.LeafSteps`: for every leaf with a nontrivial
  expansion, the compiled form takes at most `leafCost B bounds` steps from any
  state — the leaf half of the top-level step bound (stepped-flapjack#2, phase
  C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CopyLoopSteps`: the outer bitmap-list copy
  loop's bound `copyLoopSteps width (bitmaps.length - index)`, carried by an
  adapted `copyLoopThmWithin` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Statement`: the step-counted
  `stack_remove` statement shape and the `bitmapBound B` hypothesis that
  discharges the `storeConsts` bitmap-length bound at the top theorem
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Seq`: the `Seq` induction case of
  the step-counted correctness theorem, adding `steps <= leafCost * steps` to
  Flapjack's `compCorrectSeq` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Ite`: the `ite` case, adding the
  step bound to `compCorrectIf` (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.Loop`: the `loop` case, adding
  the step bound to `compCorrectLoop` along both the exit and the reentry
  branches (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.JumpLower`: the `jumpLower`
  case. It runs a program from the code, so it takes the code-bound hypothesis
  `codeBound` and concludes against the program-dependent factor `K`
  (stepped-flapjack#2, phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.RawCall`: the `rawCall` case,
  likewise concluding against `K` from the code bound (stepped-flapjack#2,
  phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CallCostBounds`: `leafCost` dominates the
  `call` constructor's return and handler bodies (stepped-flapjack#2, phase C3,
  in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.CallTail`: the `ret = none`
  `call` case, taking the code bound for the callee (stepped-flapjack#2,
  phase C3, in progress);
- `SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnNone`: the returning
  `call` with no handler, threading both the callee's code bound and the return
  continuation's structural bound (stepped-flapjack#2, phase C3, in progress).

Module names moved from `Flapjack.*` to `SteppedFlapjack.*`; declarations keep
their names in the `Flapjack` namespace. The tests are in the separate
`SteppedFlapjackTests` library, rooted at `SteppedFlapjack.Tests`.
-/
