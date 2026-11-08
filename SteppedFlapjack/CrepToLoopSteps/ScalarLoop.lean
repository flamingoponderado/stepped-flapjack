import SteppedFlapjack.LoopToWordSteps.WordSimpLoop

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps

/-- Loop programs with recursive branches and loops and loop-free basic blocks. -/
inductive ScalarLoop {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | branch {p} : LoopBranch p → ScalarLoop p
  | seq {a b} : ScalarLoop a → ScalarLoop b → ScalarLoop (.seq a b)
  | ite (cmp r ri live) {a b} : ScalarLoop a → ScalarLoop b → ScalarLoop (.ite cmp r ri a b live)
  | loop (liveIn liveOut) {body} : ScalarLoop body → ScalarLoop (.loop liveIn body liveOut)

end SteppedFlapjack.CrepToLoopSteps
