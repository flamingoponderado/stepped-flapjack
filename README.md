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

`SteppedFlapjack.Concrete.supported_counted_machine` composes the spans for a
`CallFreeSupported` singleton Pancake program. Given a returning run of
`evalPanValueFfiProgSteps` with at most `n` steps, the theorem proves that the
original Pancake compiler emits the bytes loaded into the fixture's RISC-V
machine and that the machine halts successfully within

```text
supportedMachineFactor program * n + supportedMachineOffset program
```

machine ticks. Both constants depend on the generated code and the fixed
backend configuration; `supportedMachineTicks_affine` proves this formula for
the composed clock. The factor combines the Lab factor 948 with the
flattening, Lab, uniform, native call-sequence, Word, Loop and Crep costs.
The result also states that `semanticsDecls` on the
original declarations, starting with an empty code table and clock zero,
terminates successfully with the machine's final I/O events.

`CallFreeSupported` covers a parameter-free function with scoped scalar locals,
scalar expressions, declarations, sequencing, conditionals, loops and word
returns. Names must be representable as HOL byte strings. The
counted source run uses the init-e-shaped fixture state in `Concrete.SourceState`;
its memory, FFI and layout are fixed by that fixture. The theorem additionally
requires concrete checks on the generated native code: its callee frame fits
the initialized stack, its Stack instructions are FFI- and shared-operation
free, label removal succeeds, and the emitted bytes fit the aligned code
buffer. It derives the compiler's bitmap and good-code conditions. These checks
refer to the program and configuration and can be discharged for a concrete
program; they do not quantify over a machine tick bound.

`Supported` also admits ordinary and tail calls. For function-only programs,
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
The machine clock is `callPipelineTicks`, with an affine identity in the counted
source steps for a fixed initial source clock. Its coefficient still includes
`callClockFactor`, which grows exponentially in that initial clock. When the
initial clock is selected from the source-step bound, the overall expression
therefore does not yet meet the roadmap’s code-only affine requirement.
`nested_initialized_machine` instantiates this composition with two call levels
and a six-step source execution.

`countdownFixture_machine`, `naturalCountdownFixture_machine`,
`comparisonFixture_machine` and `branchingLoopFixture_machine` instantiate the
common theorem and discharge those checks. For countdown input `n < 2^64`,
the machine clock is `167602730287449600 * (6*n+9) + 1592247331570371948`.
The comparison and branching-loop clocks are `90715439766875148` and
`36771214184170446348` respectively.

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
