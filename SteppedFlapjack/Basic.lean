import Flapjack.PanValueFfiSemantics

/-!
# stepped-flapjack

Placeholder root module.  The step-counted structured Pancake semantics
(`evalPanValueFfiProgSteps`, the clocked-to-stepped bridge, the fuel and event
monotonicity theorems, `PanCost`, and their tests) still live in Flapjack.
They move here in phase 4 of flapjack#1251, once Flapjack's compiler and its
`@[hol]`-tagged modules no longer import them.

Importing `Flapjack.PanValueFfiSemantics` here checks that this package builds
against Flapjack as a Lake dependency.
-/

namespace SteppedFlapjack

/-- The stepped FFI evaluator, reached through the Flapjack dependency. -/
example := @Flapjack.evalPanValueFfiProgSteps

end SteppedFlapjack
