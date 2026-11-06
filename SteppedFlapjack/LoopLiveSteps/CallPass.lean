import SteppedFlapjack.LoopToWordSteps.WordSimpSequence
import Flapjack.Pancake.LoopCall

/-! The Loop call pass on the supported call-free source fragment. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

/-- The call-target propagation pass leaves call-free branches unchanged,
regardless of the propagated target map. -/
theorem loopCall_branch {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ env, (loopCallCompHOL env p).1 = p := by
  induction shape with
  | skip | tick | store _ _ | setGlobal _ _ | ret _ | «break» _ | «continue» _ => intro env; simp [loopCallCompHOL]
  | assign v e => intro env; cases e <;> simp [loopCallCompHOL]
  | @seq a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL]
    rw [iha env,ihb (loopCallCompHOL env a).2]
  | mark h ih => intro env; simp only [loopCallCompHOL,ih]
  | @ite cmp r ri live a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL,iha env,ihb env]

/-- The pass is also the identity on the supported sequences of branch-bodied
loops, so frontend call propagation introduces no extra source steps. -/
theorem loopCall_sequence {p : HolLoopProg width} (shape : LoopSequenceSource p) :
    ∀ env, (loopCallCompHOL env p).1 = p := by
  induction shape with
  | branch h => exact loopCall_branch h
  | loop live exits h =>
    intro env
    simp only [loopCallCompHOL,loopCall_branch h]
  | @seq a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL]
    rw [iha env,ihb (loopCallCompHOL env a).2]

end SteppedFlapjack.LoopLiveSteps
