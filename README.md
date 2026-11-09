# stepped-flapjack

Step-counted source semantics for structured Pancake programs, split out of
[Flapjack](https://github.com/flamingoponderado/flapjack), the Lean 4 port of
the Pancake compiler. This package depends on Flapjack as a Lake package.

The code was split out in phase 4 of
[flapjack#1251](https://github.com/flamingoponderado/flapjack/issues/1251).
The revision currently pinned by init-e predates that split and still contains
the stepped definitions. At this revision, the corresponding modules here
import those existing definitions rather than redeclaring them.

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
context.
The aligned initialization construction keeps the byte-closed machine domain
separate from the word-aligned Stack domain. The earlier results that required
one nonempty domain to be both byte-closed and word-aligned have been removed;
`unalignedLabInit_incompatible` proves why those assumptions conflict.

The zero-count source has an independently proved nine-step execution and its
actual compiler artifact has at most 1,040 bytes. A concrete RISC-V theorem
with an explicit, independently fixed tick bound remains to be proved.

The concrete declaration example includes an independently counted 13-step
source execution. The previous machine theorem that selected part of its tick
bound existentially has been removed; an independently fixed machine bound
remains to be proved.

The pinned historical Flapjack revision also contains the clocked/stepped
shared FFI definitions. The expression-evaluator route and memory-aware counted
field bridge needed here live in this package.

## Building

```sh
lake exe cache get   # Mathlib cache, via Flapjack's dependency
lake build
```

The Lean toolchain matches Flapjack's (`lean-toolchain`). The `flapjack`
dependency is pinned in both `lakefile.toml` and `lake-manifest.json` to the
same revision as init-e. To change it, update the revision in `lakefile.toml`
and run `lake update flapjack`.

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
