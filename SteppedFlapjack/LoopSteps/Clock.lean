import SteppedFlapjack.LoopToWordSteps.Sequence
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers

/-! Stability of Loop step counts when a completed run gets more clock. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- Adding clock preserves the visited-node count for non-timeout runs of
Loop programs made from direct leaves, sequencing and marks. -/
theorem directProgram_steps_add_clock {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : DirectProgram p)
    (s final : LoopSemStateFiniteExact width F) (res : Option (LoopResultExact width))
    (run : evaluate p s = (res,final)) (nonTimeout : res ≠ some .timeOut) (extra : Nat) :
    steps p {s with clock := s.clock + extra} = steps p s := by
  induction shape generalizing s final res with
  | @leaf q leaf =>
    have h : ∀ t : LoopSemStateFiniteExact width F, steps q t = 1 := by
      intro t
      apply steps_leaf
      cases leaf <;> rfl
    rw [h,h]
  | mark shape ih =>
    rw [steps_mark,steps_mark]
    apply congrArg (Nat.add 1)
    apply ih s final res
    · simpa only [evaluate] using run
    · exact nonTimeout
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,steps_seq]
    rcases firstRun : evaluate a s with ⟨firstRes,middle⟩
    have firstNotTimeout : firstRes ≠ some .timeOut := by
      intro bad
      have whole := run
      rw [evaluate_seq,firstRun,bad] at whole
      cases whole
      exact nonTimeout rfl
    have firstLift := evaluate_add_clock_eq a s firstRes middle extra firstRun firstNotTimeout
    rw [firstLift]
    have firstSteps := iha s middle firstRes firstRun firstNotTimeout
    rw [firstSteps]
    cases firstRes with
    | some r => rfl
    | none =>
      have secondRun : evaluate b middle = (res,final) := by
        rw [evaluate_seq,firstRun] at run
        exact run
      have secondSteps := ihb middle final res secondRun nonTimeout
      simpa only using congrArg (fun n => 1 + steps a s + n) secondSteps

end SteppedFlapjack.LoopSteps
