import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile
import SteppedFlapjack.WordToStackSteps.NormalizedClock

/-! Clock-based visit bounds for non-nested Word loop sequences. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open SteppedFlapjack.WordToStackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A branch-bodied loop has at most its syntax size times the available clock
plus one in actual evaluator visits, including timeout and cut failure. -/
theorem branchLoop_clock_bound (names exits : Spt Unit)
    {body : WordLangProgHOL (BitVec width)} (shape : Branch body)
    (s : WordSemStateFiniteExact width C F) :
    steps (.loop names body exits) s ≤ sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) * (s.clock+1) := by
  induction hc : s.clock using Nat.strongRecOn generalizing s with
  | _ clock ih =>
    have sizeLower : sizeOf body + 1 ≤ sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) := by simp_wf; omega
    rw [steps_loop]
    rcases cut : cutState (names,.ln) s with _ | entry
    · simp only
      simp_wf
      nlinarith
    · simp only
      have static := branch_static shape entry
      rcases run : evaluate body entry with ⟨result,post⟩
      by_cases cont : wordSemContLoop result ∧ post.clock ≠ 0
      · have cutClock := cutState_clock_termdep _ _ _ cut
        have runClock := evaluate_clock body entry result post run
        have smaller : (decClock post).clock < s.clock := by simp only [decClock]; omega
        have rest := ih _ (by simpa [hc] using smaller) (decClock post) rfl
        simp only [cont.1,true_and,if_pos cont.2]
        nlinarith
      · simp only [cont,if_false]
        nlinarith

/-- A sequence of branch-bodied loops has a visit bound linear in the
available clock, with a factor calculated from its syntax. -/
theorem loopSequence_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p * (s.clock+1) := by
  induction shape generalizing s with
  | branch h =>
    have bound := branch_static h s
    nlinarith
  | loop names exits h => exact branchLoop_clock_bound names exits h s
  | @seq a b ha hb iha ihb =>
    have sizeLower : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf
    rw [steps_seq]
    have first := iha s
    rcases run : evaluate a s with ⟨result,post⟩
    cases result with
    | some r => simp only; nlinarith
    | none =>
      have second := ihb post
      have clock := (evaluate_clock a s none post run).1
      simp only
      nlinarith

end SteppedFlapjack.WordSimpSteps
