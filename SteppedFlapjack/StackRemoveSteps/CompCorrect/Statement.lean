import SteppedFlapjack.StackRemoveSteps.LeafSteps
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect

/-! Statement infrastructure for phase C3 of stepped-flapjack#2: the
step-counted `stack_remove` correctness theorem.

`compCorrectWithinSteps` will conclude, in addition to Flapjack's `compCorrect`,
that the compiled run takes at most `leafCost B bounds program * steps
(program, source)` steps, where `leafCost` is the program-dependent factor of
`SteppedFlapjack/StackRemoveSteps/Defs.lean`.

The `.storeConsts` expansion's cost is `storeConstsSteps width B`, and `B` must
bound the bitmap length at the node's run-time state. `install` appends to
`source.bitmaps`, so the initial length does not bound later states; instead the
theorem carries `bitmapBound B`, a hypothesis over every pair of states related
by `stateRelHOL`. That hypothesis is carried up to the top theorem and
discharged there for the concrete program, which is where the memory layout is
known. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

/-- Every source state related to a target by `stateRelHOL` has at most `B`
bitmap words. The `stack_remove` correctness induction carries this hypothesis
unchanged; it is discharged once, at the top, for the concrete program. -/
def bitmapBound (B : Nat) : Prop :=
  ∀ (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F),
    stateRelHOL jump bounds pointer source target → source.bitmaps.length ≤ B

end SteppedFlapjack.StackRemoveSteps.CompCorrect
