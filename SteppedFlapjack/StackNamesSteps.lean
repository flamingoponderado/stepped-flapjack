import SteppedFlapjack.StackNamesSteps.CompCorrect
import SteppedFlapjack.StackNamesSteps.StepsPreservation
import SteppedFlapjack.StackNamesSteps.Semantics

/-!
# Step preservation for `stack_names`

Adapted copies of Flapjack's `stack_names` correctness proof in which the
StackSem step count is preserved (stepped-flapjack#2, phase C2).

- `CompCorrect`: Flapjack's `comp_correct` copied unchanged, so that the step
  theorem does not import the original correctness theorem.
- `StepsPreservation`: `steps_progCompHOL`, the step count of the renamed
  program equals that of the source; `compCorrectWithin` conjoins it with
  `comp_correct`, and `compCorrect_of_within` forgets it.
- `Semantics`: `renameState_makeInit`, the `compile_semantics_alt` step of
  `make_init_semantics`, and `stackNamesSemanticsWithin`, the bounded entry run
  from `make_init` to the target state.
-/
