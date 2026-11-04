import SteppedFlapjack.StackSteps.Defs

/-! Checks of the StackSem step count. -/

namespace SteppedFlapjack.Test.StackSteps

open Flapjack Flapjack.Compiler.Backend.StackLang SteppedFlapjack.StackSteps

variable {C F : Type} (s : StackSemStateFiniteExact 64 C F)

-- A leaf takes one step.
example : steps ((.skip : HolProg 64), s) = 1 := steps_leaf _ _ rfl

-- `Seq skip skip` takes three: the `Seq` node and both leaves.
example : steps ((.seq .skip .skip : HolProg 64), s) = 3 := by
  rw [steps_seq, steps_leaf _ _ rfl, StackSemEvaluate.evaluate_skip]
  simp [StackSemControl.fixClock, steps_leaf _ _ (rfl : isRecursive (.skip : HolProg 64) = false)]

end SteppedFlapjack.Test.StackSteps
