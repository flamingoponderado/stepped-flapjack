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

The `*Steps` directories contain the quantitative compiler chain:
Pancake → Crep → Loop → Word passes → Stack → Lab → RISC-V.

## Source-to-machine bound

`SteppedFlapjack.Concrete.countedCalls_initializedMachine` composes the spans
from a counted Pancake source return to a successfully halting initialized
RISC-V machine. It proves the emitted compiler bytes and bitmaps, source
semantics, and matching I/O events at an explicit machine clock.

`Supported` admits ordinary and tail calls as well as scalar declarations,
sequencing, conditionals, loops, and word returns. For function-only programs,
`FunctionTableSupported` requires scalar parameters and return shapes, scoped
call-aware bodies, and byte-representable names. `countedCalls_initializedMachine`
uses those declarations and a counted source return to derive the actual
compiler output, matching source and machine behavior, and an explicit machine
tick expression. Its concrete checks include code size, alignment, native
stack safety and call-graph capacity; the capacity check can reject recursion.
It also requires that the compiler select no functions for inlining and that
the source heap headers use the bitmap count computed by the compiler. These
conditions and the fixed fixture layout are gaps relative to init-e's actual
initialization and guest.
The machine clock is `callPipelineTicks`. Its coefficient in the counted
source-step bound depends on the compiled code and function table. The
Crep-to-Loop factor is independent of the initial source clock; that clock
appears separately and linearly in the complete expression. Thus choosing an
initial clock that is affine in the source-step bound retains an affine machine
tick bound.
`nested_initialized_machine` instantiates this composition with two call levels
and a six-step source execution.

`comparisonFixture_machine` and `branchingLoopFixture_machine` instantiate the
call-aware theorem with concrete clocks `comparisonTicks` and
`branchingLoopTicks`. Both `countdownFixture_machine` and
`naturalCountdownFixture_machine` state the kernel-checked bound
`44195828396580057600 * (6*n+9) + 59847410146165518348` machine ticks.

This fragment and fixture do not yet cover init-e's full guest: globals, heap
and shared-memory operations, exceptions, FFI, primitive behavior and host
input are part of the widening work in the
[roadmap](https://github.com/flamingoponderado/stepped-flapjack/issues/19).
The eventual theorem must apply to init-e's `Guest.Software.guestAst` and
`InitE.sourceBehaviour` with its actual initialization and host input.

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
