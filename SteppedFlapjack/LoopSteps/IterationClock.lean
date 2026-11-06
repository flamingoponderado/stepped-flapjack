import SteppedFlapjack.LoopSteps.BranchedStatic
import Mathlib.Tactic.Linarith

/-! Runtime visit bounds for loops with loop-free bodies. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- A Loop loop with a loop-free body visits at most a body-size factor per
clock unit consumed, plus one final iteration. This includes timeout and error
results and does not assume any compiler simulation. -/
theorem loop_steps_by_clock_consumption {width : Nat} [NeZero width] {F : Type}
    (live liveOut : NumSet) (body : HolLoopProg width) (shape : BranchedProgram body)
    (source final : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate (.loop live body liveOut) source = (result,final)) :
    steps (.loop live body liveOut) source ≤
      (1 + sizeOf body) * (source.clock - final.clock + 1) := by
  induction hc : source.clock using Nat.strongRecOn generalizing source final result with
  | _ clock ih =>
    rcases cutRun : cutRes live (none,source) with ⟨cutResult,entry⟩
    cases cutResult with
    | some r =>
      rw [steps_loop,cutRun]
      simp only
      have budget : 1 ≤ clock - final.clock + 1 := by omega
      nlinarith
    | none =>
      rcases bodyRun : evaluate body entry with ⟨bodyResult,post⟩
      have entryClock := cutRes_none_clock cutRun
      have bodyClock := evaluate_clock body entry bodyResult post bodyRun
      have bodyBound := branchedProgram_static_bound shape entry
      have execution := run
      rw [evaluate,cutRun] at execution
      simp only at execution
      rw [fix_clock_evaluate,bodyRun] at execution
      simp only [← hc] at *
      rw [steps_loop,cutRun]
      simp only
      rw [bodyRun]
      by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
      · have recurRun : evaluate (.loop live body liveOut) post = (result,final) := by
          rcases continuing with h | h <;> rw [h] at execution <;> exact execution
        have smaller : post.clock < source.clock := by omega
        have recur := ih post.clock smaller post final result recurRun rfl
        have finalClock := evaluate_clock (.loop live body liveOut) post result final recurRun
        have budget : post.clock - final.clock + 1 + 1 ≤ source.clock - final.clock + 1 := by omega
        have scaled := Nat.mul_le_mul_left (1 + sizeOf body) budget
        rcases continuing with h | h <;> rw [h] <;> simp only
        all_goals nlinarith
      · have hnone : bodyResult ≠ none := fun h => continuing (Or.inl h)
        have hcont : bodyResult ≠ some (.continue 0) := fun h => continuing (Or.inr h)
        cases bodyResult with
        | none => exact (hnone rfl).elim
        | some r =>
          cases r <;> try (simp only; nlinarith)
          case «continue» label =>
            cases label with
            | zero => exact (hcont rfl).elim
            | succ n => simp only; nlinarith

end SteppedFlapjack.LoopSteps
