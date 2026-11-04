import SteppedFlapjack.StackSteps.Defs

/-!
# Tick bounds for the `stack_to_lab` simulation

Definitions for the bounded copy of Flapjack's `stack_to_lab`
`flatten_correct` (stepped-flapjack#2, phase C1).

The flattened code of one StackSem node executes at most
`flattenStepFactor` LabSem instructions of its own; the instructions of its
sub-programs are counted by their own nodes. The worst case is a returning
call with an exception handler that returns normally: the `LocValue` of the
return label, the jump into the callee and the jump over the handler. An `If`
takes at most two (the conditional jump and the join jump), `FFI` and
`Install` two, a loop iteration one (the back jump), and leaves at most one.
Each LabSem instruction takes one clock tick (`Halt` and final FFI outcomes
take none), so the ticks of a run are bounded by
`flattenStepFactor * steps (prog, s)`.

This is stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.StackToLabSteps

/-- The LabSem instructions executed per StackSem step. -/
def flattenStepFactor : Nat := 3

end SteppedFlapjack.StackToLabSteps
