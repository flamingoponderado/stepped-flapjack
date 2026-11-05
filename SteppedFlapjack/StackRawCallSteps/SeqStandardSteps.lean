import SteppedFlapjack.StackRawCallSteps.LoopSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Standard
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open SteppedFlapjack.StackSteps

/-- The unchanged sequence form preserves a nonincreasing step bound. -/
theorem standardSeqWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (firstIH : ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (first, source) = (r, u) ∧ r ≠ some .error ∧ stateRel i source t →
      SimulationWithin (comp i first) i t u r (steps (first, source)))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F), evaluate (first, source) = (none, middle) →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (second, middle) = (r, u) ∧ r ≠ some .error ∧ stateRel i middle t →
      SimulationWithin (comp i second) i t u r (steps (second, middle)))
    (hypothesis : evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (.seq (comp info first) (comp info second)) info target post result
      (steps (.seq first second, source)) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨firstClock, targetMiddle, firstSpace, middleRelation, firstTargetRun, firstGuard, firstCost⟩ :=
        firstIH info target middle none ⟨firstRun, by simp, relation⟩
      have spaceEq := firstGuard (by simp)
      subst firstSpace
      have spaceSelf : { targetMiddle with stackSpace := targetMiddle.stackSpace } = targetMiddle := by
        cases targetMiddle; rfl
      rw [spaceSelf] at firstTargetRun
      obtain ⟨secondClock, targetPost, finalSpace, postRelation, secondTargetRun, finalGuard, secondCost⟩ :=
        secondIH middle firstRun info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
      have extendedFirst := Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp info first) { target with clock := target.clock + firstClock }
        none targetMiddle ⟨firstTargetRun, by simp⟩
      have inputEq : { { target with clock := target.clock + firstClock } with
          clock := ({ target with clock := target.clock + firstClock }).clock + secondClock } =
          { target with clock := target.clock + (firstClock + secondClock) } := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedFirst
      have extendedCost : steps (comp info first, {target with clock := target.clock + (firstClock + secondClock)}) =
          steps (comp info first, {target with clock := target.clock + firstClock}) := by
        simpa only [Nat.add_assoc] using steps_addClock secondClock _ _ _ rfl none targetMiddle firstTargetRun (by simp)
      refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard, ?_⟩
      · rw [evaluateSeqUnclamped, extendedFirst]
        exact secondTargetRun
      · rw [steps_seq_run _ _ _ _ extendedFirst, steps_seq_run _ _ _ _ firstRun, extendedCost]
        exact Nat.add_le_add (Nat.add_le_add_left firstCost 1) secondCost
  | some firstResult =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      obtain ⟨clock, targetPost, finalSpace, postRelation, targetRun, guard, cost⟩ :=
        firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
      refine ⟨clock, targetPost, finalSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateSeqUnclamped, targetRun]
      · rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun,
          steps_seq, StackSemEvaluateClock.fixClockEvaluate, firstRun]
        simp only [Nat.add_zero]
        exact Nat.add_le_add_left cost 1
end SteppedFlapjack.StackRawCallSteps
