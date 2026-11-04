import SteppedFlapjack.StackToLabSteps.Defs
import SteppedFlapjack.StackToLabSteps.LabClock
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Statement
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Leaves
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Control
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.If
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Loop
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Jumps
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Call
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Guarded
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Install
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.ShMem
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Ffi
import SteppedFlapjack.StackToLabSteps.FlattenCorrect
import SteppedFlapjack.StackToLabSteps.FlattenCallCorrect
import SteppedFlapjack.StackToLabSteps.FlattenSemantics

/-!
# Bounded `stack_to_lab` simulation

Adapted copies of Flapjack's `stack_to_lab` `flatten_correct` proof in which
the LabSem run is bounded (stepped-flapjack#2, phase C1). `flattenCorrectWithin`
matches a StackSem run of `prog` from `s1` by a LabSem run of at most
`flattenStepFactor * steps (prog, s1)` ticks, with `flattenStepFactor = 3`.
`flattenSemanticsWithin` lifts this to the start call: an entry run that
completes within `n` steps is matched by a LabSem run from clock at most
`flattenStepFactor * (n + h)` with the same outcome and I/O events, where `h`
bounds the steps of the halting procedure 1 when it is reached.
`evaluate_subClock` removes unused clock from a LabSem run.
-/
