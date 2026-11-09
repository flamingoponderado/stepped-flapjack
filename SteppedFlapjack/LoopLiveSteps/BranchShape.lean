import SteppedFlapjack.CrepToLoopSteps.ScalarLoop
import SteppedFlapjack.LoopSteps.BranchedStatic

namespace SteppedFlapjack.LoopLiveSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

theorem branch_branched {p : HolLoopProg width} (shape : LoopBranch p) : BranchedProgram p := by
  induction shape with
  | skip => exact .leaf .skip
  | tick => exact .leaf .tick
  | assign v e => exact .leaf (.assign v e)
  | store e v => exact .leaf (.store e v)
  | setGlobal v e => exact .leaf (.setGlobal v e)
  | ret vs => exact .leaf (.ret vs)
  | «break» n => exact .leaf (.break n)
  | «continue» n => exact .leaf (.continue n)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | mark _ ih => exact .mark ih
  | ite cmp r ri live _ _ ih1 ih2 => exact .ite cmp r ri live ih1 ih2

end SteppedFlapjack.LoopLiveSteps
