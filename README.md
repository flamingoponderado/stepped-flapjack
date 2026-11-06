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
- Flapjack-specific clocked-evaluator fuel monotonicity, clock/timeout contracts,
  and clock-shift prerequisites: `SteppedFlapjack.PanValueFfiClockFuel`,
  `SteppedFlapjack.PanValueFfiClockCorrectness`, and
  `SteppedFlapjack.PanValueFfiClockShift`; these describe the fuel-indexed
  evaluator and are not direct ports of HOL declarations;
- the clocked-to-stepped bridge: `SteppedFlapjack.PanValueFfiClockProjection`
  and `SteppedFlapjack.PanValueFfiClockStepsBridge`;
- `SteppedFlapjack.PanCost`, the source-level resource model built on step
  counts;
- `SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge`, the
  counted expression evaluator against `PanSem`;
- their tests, under `SteppedFlapjack/Test/`, in the separate
  `SteppedFlapjackTests` library. They are compile-time checks, so
  `lake build` runs them. They do not import Flapjack's test modules: the
  fixtures they need are copied from the Flapjack tests they were split from,
  and `SteppedFlapjack.Test.PanValueFfiSemantics` holds the shared stateful-FFI
  fixtures.

The `*Steps` directories also contain the quantitative compiler chain:
Pancake → Crep → Loop → Word passes → Stack → Lab → RISC-V. The
`PanToCrepSteps` modules connect counted source execution to global lowering,
including a scalar declaration around an initialized loop. The general
`panOriginalDeclEntry_riscvWithin` theorem carries a source control-step bound
through this chain under the stated state and compilation conditions.

`counted_singleEntry_declared_fullCompiler_riscv` takes a separately bounded,
successful fine-grained Pancake execution of a supported scalar assignment loop
and gives a RISC-V halt bound for the original singleton program's full compiler
output. The bound depends on the program and backend configuration; the result
covers successful return and resource exhaustion. The theorem assumes the
stated source clock, source layout, compiler input, and full-initialization
machine relations. `labInitialized_counted_declared_fullCompiler_riscv` constructs the
source and native inputs for this supported fragment from a Lab initialization
context. Its `withClock` variant derives a sufficient proof clock from the
source budget without changing the counted run or RISC-V machine.
`labInitialized_countdown_fullCompiler_riscv` applies the chain to a
countdown. Concrete initialization guards remain to be proved for
an application.

The reusable concrete declaration example is kept in the library because it
instantiates the actual global entry and serves as an end-to-end proof target.
`concreteDecl_counted_riscv_bounded` gives its 13-step source execution a common
machine-step bound covering both successful entry and a resource-limit
outcome, parameterized by any supplied source budget of at least 13. The bound computes the entry bitmap, frame and source expressions
from compiler output and still depends on oracle prefix costs. The theorem
assumes matching source, native Stack, Lab and
RISC-V initial states, native initialization and backend relations. It does
not yet construct a concrete machine state or prove a general bridge from
arbitrary counted source runs to `controlSteps`. The bounded theorem starts
from an original state with empty locals, globals, exceptions and structures,
and a concrete source code table; it constructs the lowered entry from that
state. Earlier intermediate lemmas still use the reverse construction.

The declaration chain currently duplicates much of the earlier tail-entry
chain, including backend premises. Factoring the chain over supported callee
shapes and a proved shape-specific limit remains work in progress. The counted
loop and declaration examples are imported as reusable proofs for the
concrete result; standalone compile-time fixtures remain in
`SteppedFlapjack/Test/`.

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

## Checks

CI runs an axiom audit (`SteppedFlapjack/Test/Axioms.lean`, elaborated afresh
with `lake lean`): it fails if any declaration of a `SteppedFlapjack` module,
private ones included, depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`, which also rejects `sorry`, or if a
non-test source file is not imported through `SteppedFlapjack`. It then runs
`scripts/check-warnings.sh`, which fails on any warning outside
`SteppedFlapjack/Test/`.
