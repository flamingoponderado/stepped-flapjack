import SteppedFlapjack.LoopSteps.BranchedClock
import SteppedFlapjack.LoopSteps.IterationClock

/-! Clock-shift stability for actual loop visit counts. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- Adding clock to a non-timeout loop with a loop-free body preserves its
actual number of evaluator visits. -/
theorem branchedLoop_steps_add_clock {width : Nat} [NeZero width] {F : Type}
    (live liveOut : NumSet) (body : HolLoopProg width) (shape : BranchedProgram body)
    (source final : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate (.loop live body liveOut) source = (result,final))
    (nonTimeout : result ≠ some .timeOut) (extra : Nat) :
    steps (.loop live body liveOut) {source with clock := source.clock + extra} =
      steps (.loop live body liveOut) source := by
  induction hc : source.clock using Nat.strongRecOn generalizing source final result with
  | _ clock ih =>
    rcases cutRun : cutRes live (none,source) with ⟨cutResult,entry⟩
    cases cutResult with
    | some r =>
      have cutNotTimeout : some r ≠ some .timeOut := by
        intro bad
        have whole := run
        rw [evaluate,cutRun] at whole
        simp only at whole
        have : result = some r := (Prod.mk.inj whole).1.symm
        exact nonTimeout (this.trans bad)
      have cutShift := cutRes_add_clock live none source entry (some r) extra cutRun cutNotTimeout
      simp only [← hc]
      rw [steps_loop,steps_loop,cutRun,cutShift]
    | none =>
      rcases bodyRun : evaluate body entry with ⟨bodyResult,post⟩
      have entryClock := cutRes_none_clock cutRun
      have bodyClock := evaluate_clock body entry bodyResult post bodyRun
      have execution := run
      rw [evaluate,cutRun] at execution
      simp only at execution
      rw [fix_clock_evaluate,bodyRun] at execution
      have bodyNotTimeout : bodyResult ≠ some .timeOut := by
        intro bad
        rw [bad] at execution
        simp only [LoopSemStateFiniteExact.exitLoop,Prod.mk.injEq] at execution
        exact nonTimeout execution.1.symm
      have cutShift := cutRes_add_clock live none source entry none extra cutRun (by simp)
      have bodyShift := evaluate_add_clock_eq body entry bodyResult post extra bodyRun bodyNotTimeout
      have bodySteps := branchedProgram_steps_add_clock shape entry post bodyResult bodyRun bodyNotTimeout extra
      simp only [← hc]
      rw [steps_loop,steps_loop,cutRun,cutShift]
      simp only
      rw [bodyRun,bodyShift,bodySteps]
      by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
      · have recurRun : evaluate (.loop live body liveOut) post = (result,final) := by
          rcases continuing with h | h <;> rw [h] at execution <;> exact execution
        have smaller : post.clock < clock := by omega
        have recur := ih post.clock smaller post final result recurRun nonTimeout rfl
        rcases continuing with h | h <;> rw [h] <;> simp only
        all_goals rw [recur]
      · cases bodyResult with
        | none => exact (continuing (Or.inl rfl)).elim
        | some r =>
          cases r <;> try rfl
          case «continue» label =>
            cases label with
            | zero => exact (continuing (Or.inr rfl)).elim
            | succ n => rfl

end SteppedFlapjack.LoopSteps
