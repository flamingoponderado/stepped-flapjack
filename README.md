# stepped-flapjack

Step-counted source semantics for structured Pancake programs, split out of
[Flapjack](https://github.com/flamingoponderado/flapjack), the Lean 4 port of
the Pancake compiler. This package depends on Flapjack as a Lake package.

The code moved here in phase 4 of
[flapjack#1251](https://github.com/flamingoponderado/flapjack/issues/1251).

## Why a separate package

Flapjack has two source evaluators for structured Pancake programs:

- the **clocked** evaluator (`PanValueFfiClockSemantics`, `PanSem`), which
  follows CakeML's `panSem`, including its clock and timeouts. Flapjack's
  HOL-shaped observational semantics and divergence use this one;
- the **stepped** evaluator (`evalPanValueFfiProgSteps`,
  `PanSteppedSemantics`), which counts source evaluation steps but has no
  clock. When it runs out of fuel it returns `none` and drops the FFI state,
  and a zero-clock `Tick` does not time out.

No stepped module has a `@[hol]` tag. Because the stepped evaluator has no
timeouts, the bridge from clocked to stepped results cannot cover timed-out
runs, and HOL needs exactly those runs to define divergence. Flapjack's
compiler and its HOL correspondence therefore do not need the stepped code,
so it is moving here.

## Contents

Module names changed from `Flapjack.*` to `SteppedFlapjack.*`. Declarations
keep their names in the `Flapjack` namespace.

- the counted expression evaluators: `SteppedFlapjack.PanValueExpCounted` and
  `SteppedFlapjack.PanExpressionEvaluator`;
- the stepped evaluators: `SteppedFlapjack.PanValueFfiSemantics`
  (`evalPanValueFfiProgSteps` and its program wrappers) and
  `SteppedFlapjack.PanSteppedSemantics`;
- the fuel and event monotonicity theorems: `SteppedFlapjack.PanValueFfiFuel`
  and `SteppedFlapjack.PanValueFfiEventMonotonicity`;
- the clocked-to-stepped bridge: `SteppedFlapjack.PanValueFfiClockProjection`
  and `SteppedFlapjack.PanValueFfiClockStepsBridge`;
- `SteppedFlapjack.PanCost`, the source-level resource model built on step
  counts;
- `SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge`, the
  counted expression evaluator against `PanSem`;
- their tests, under `SteppedFlapjack/Test/`. They are compile-time checks, so
  `lake build` runs them. Several build on the fixtures of the matching
  `Flapjack.Test.*` modules, which stay in Flapjack.

Code shared with the clocked evaluator stays in Flapjack, in
`Flapjack.PanValueFfiCore` and `Flapjack.PanExpressionEvaluatorBase`.

## Building

```sh
lake exe cache get   # Mathlib cache, via Flapjack's dependency
lake build
```

The Lean toolchain matches Flapjack's (`lean-toolchain`). Flapjack is pinned
in `lake-manifest.json`; `lake update Flapjack` moves the pin to Flapjack's
current `main`.

## License

BSD 3-Clause, the same as Flapjack. See [`LICENSE`](LICENSE) and
[`COPYRIGHT`](COPYRIGHT) for the upstream CakeML and HOL4 notices that apply
to the ported code.
