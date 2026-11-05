import SteppedFlapjack.LoopToWordSteps.Conditional
import Flapjack.Pancake.Proofs.LoopToWord.TickUnfold

/-! Cost of the Loop-to-Word loop wrapper. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.WordSemStateFiniteExact

/-- The `tick; (loop; tick)` wrapper adds at most four WordSem visits beyond
its loop. No assumptions about the loop outcome or clock are needed. -/
theorem tickLoopTick_steps_bound {width : Nat} [NeZero width] {C F : Type}
    (live exit : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) s ≤
      4 + WordSteps.steps (.loop live body exit) (decClock s) := by
  rw [WordSteps.steps_seq, WordSemStateFiniteExact.evaluate]
  have tick : WordSteps.steps (.tick : WordLangProgHOL (BitVec width)) s = 1 :=
    WordSteps.steps_leaf _ _ rfl
  rw [tick]
  by_cases zero : s.clock = 0
  · simp [zero]; omega
  · simp only [zero, if_false]
    have inner := WordSteps.steps_seq (.loop live body exit) .tick (decClock s)
    rw [inner]
    rcases run : evaluate (.loop live body exit) (decClock s) with ⟨out,post⟩
    cases out with
    | none =>
      have lastTick : WordSteps.steps (.tick : WordLangProgHOL (BitVec width)) post = 1 :=
        WordSteps.steps_leaf _ _ rfl
      simp only [lastTick]
      omega
    | some result => simp only; omega

/-- A wrapper iteration expands to its body cost, optional loop re-entry,
and fixed administrative overhead. -/
theorem tickLoopTick_iteration_bound {width : Nat} [NeZero width] {C F : Type}
    (live exit : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s entered post : WordSemStateFiniteExact width C F) (out : Option (WordSemResult width))
    (cut : cutState (live,.ln) (decClock s) = some entered)
    (bodyRun : evaluate body entered = (out,post)) :
    WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) s ≤
      5 + WordSteps.steps body entered +
        (if wordSemContLoop out ∧ post.clock ≠ 0 then WordSteps.steps (.loop live body exit) (decClock post) else 0) := by
  have h := tickLoopTick_steps_bound live exit body s
  rw [WordSteps.steps_loop,cut] at h
  simp only at h
  rw [bodyRun] at h
  simp only at h
  omega


/-- With a nonzero clock, the loop inside the wrapper cannot cost more than
the entire wrapped execution. -/
theorem loop_steps_le_tickLoopTick {width : Nat} [NeZero width] {C F : Type}
    (live exit : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (nonzero : s.clock ≠ 0) :
    WordSteps.steps (.loop live body exit) (decClock s) ≤
      WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) s := by
  rw [WordSteps.steps_seq,WordSemStateFiniteExact.evaluate]
  simp only [nonzero,if_false]
  have inner := WordSteps.steps_seq (.loop live body exit) .tick (decClock s)
  rw [inner]
  rcases run : evaluate (.loop live body exit) (decClock s) with ⟨out,post⟩
  cases out <;> simp only <;> omega

/-- On a continuing iteration, the complete wrapped re-entry gives a
compositional bound for the current wrapped iteration. -/
theorem tickLoopTick_continue_bound {width : Nat} [NeZero width] {C F : Type}
    (live exit : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s entered post : WordSemStateFiniteExact width C F) (out : Option (WordSemResult width))
    (cut : cutState (live,.ln) (decClock s) = some entered)
    (bodyRun : evaluate body entered = (out,post))
    (continues : wordSemContLoop out = true) (nonzero : post.clock ≠ 0) :
    WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) s ≤
      5 + WordSteps.steps body entered +
        WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) post := by
  have first := tickLoopTick_iteration_bound live exit body s entered post out cut bodyRun
  have second := loop_steps_le_tickLoopTick live exit body post nonzero
  simp only [continues, true_and, if_pos nonzero] at first
  omega

end SteppedFlapjack.LoopToWordSteps
