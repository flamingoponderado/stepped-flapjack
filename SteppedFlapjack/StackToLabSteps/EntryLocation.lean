import Flapjack.Pancake.CrepToLoop
import Flapjack.Compiler.Backend.BvlToBvi

/-! The Pancake entry and the backend initialization entry coincide. -/
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.Compiler.Backend

/-- The first compiled Pancake function occupies the backend's initialization
entry location. Both are fixed by the respective HOL compiler definitions. -/
theorem firstLoopName_eq_initGlobalsLocation :
    firstLoopName = BvlToBvi.initGlobalsLocation := by decide

end SteppedFlapjack.StackToLabSteps
