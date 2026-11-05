import SteppedFlapjack.StackRawCallSteps.IfSteps
import SteppedFlapjack.StackSteps.AddClock
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Loop
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.LoopCase
open SteppedFlapjack.StackSteps

/-- A loop that exits after its body does not increase the counted steps. -/
theorem loopExitWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, post))
    (exit : contLoop result = false)
    (bodySimulation : SimulationWithin (comp info body) info target post result (steps (body, source))) :
    SimulationWithin (comp info (.loop body)) info target post (exitLoop result)
      (steps (.loop body, source)) := by
  obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ := bodySimulation
  refine ⟨clock, targetState, stackSpace, postRelation, ?_, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp [exit]
  · intro exitGuard
    exact guard (exitLoopGuard result exitGuard)
  · simp only [comp]
    rw [steps_loop_exit _ _ _ _ targetExecution (by simp [exit]),
      steps_loop_exit _ _ _ _ execution (by simp [exit])]
    omega

/-- A loop whose continuing body reaches zero clock has the same timeout
and a nonincreasing step count. -/
theorem loopTimeoutWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, post))
    (continuing : contLoop result = true) (zero : post.clock = 0)
    (bodySimulation : SimulationWithin (comp info body) info target post result (steps (body, source))) :
    SimulationWithin (comp info (.loop body)) info target (emptyEnv post) (some .timeOut)
      (steps (.loop body, source)) := by
  obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ := bodySimulation
  have spaceEq := guard (contLoopGuard result continuing)
  subst stackSpace
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  rw [stackSelf] at targetExecution
  have targetZero : targetState.clock = 0 := (stateRel_clock info post targetState postRelation).trans zero
  refine ⟨clock, emptyEnv targetState, (emptyEnv targetState).stackSpace,
    stateRel_emptyEnv info post targetState postRelation, ?_, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [continuing, if_true]
    rw [if_pos targetZero]
  · intro impossible
    exact False.elim (impossible.1 rfl)
  · simp only [comp]
    rw [steps_loop_exit _ _ _ _ targetExecution (by simp [targetZero]),
      steps_loop_exit _ _ _ _ execution (by simp [zero])]
    omega

/-- Continuing loop iterations preserve the nonincreasing step bound. -/
theorem loopReentryWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (info : Spt Nat)
    (source target bodyPost post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyExecution : evaluate (body, source) = (bodyResult, bodyPost))
    (continuing : contLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (bodySimulation : SimulationWithin (comp info body) info target bodyPost bodyResult (steps (body, source)))
    (reentryIH : ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (.loop body, decClock bodyPost) = (r, u) ∧ r ≠ some .error ∧ stateRel i (decClock bodyPost) t →
      SimulationWithin (comp i (.loop body)) i t u r (steps (.loop body, decClock bodyPost)))
    (execution : evaluate (.loop body, decClock bodyPost) = (result, post))
    (nonerror : result ≠ some .error) :
    SimulationWithin (comp info (.loop body)) info target post result (steps (.loop body, source)) := by
  obtain ⟨clock, targetBody, stackSpace, bodyRelation, targetBodyExecution, bodyGuard, bodyCost⟩ := bodySimulation
  have continuationGuard := contLoopGuard bodyResult continuing
  have spaceEq := bodyGuard continuationGuard
  subst stackSpace
  have stackSelf : { targetBody with stackSpace := targetBody.stackSpace } = targetBody := by
    cases targetBody
    rfl
  rw [stackSelf] at targetBodyExecution
  have recursiveRelation := stateRel_decClock info bodyPost targetBody bodyRelation
  obtain ⟨recursiveClock, targetPost, finalSpace, postRelation, targetExecution, guard, recursiveCost⟩ :=
    reentryIH info (decClock targetBody) post result ⟨execution, nonerror, recursiveRelation⟩
  have targetClockEq := stateRel_clock info bodyPost targetBody bodyRelation
  have targetNonzero : targetBody.clock ≠ 0 := by
    simpa only [targetClockEq] using nonzero
  have extendedBody := Compiler.Backend.StackProps.evaluateAddClock recursiveClock
    (comp info body) { target with clock := target.clock + clock }
    bodyResult targetBody ⟨targetBodyExecution, continuationGuard.1⟩
  have inputEq : { { target with clock := target.clock + clock } with
      clock := ({ target with clock := target.clock + clock }).clock + recursiveClock } =
      { target with clock := target.clock + (clock + recursiveClock) } := by
    simp only [Nat.add_assoc]
  rw [inputEq] at extendedBody
  have reentryEq : decClock { targetBody with clock := targetBody.clock + recursiveClock } =
      { decClock targetBody with clock := (decClock targetBody).clock + recursiveClock } := by
    simp only [decClock]
    congr 1
    omega
  have extendedCost : steps (comp info body, {target with clock := target.clock + (clock + recursiveClock)}) =
      steps (comp info body, {target with clock := target.clock + clock}) := by
    simpa only [Nat.add_assoc] using steps_addClock recursiveClock _ _ _ rfl bodyResult targetBody
      targetBodyExecution continuationGuard.1
  refine ⟨clock + recursiveClock, targetPost, finalSpace, postRelation, ?_, guard, ?_⟩
  · rw [comp, evaluateLoopUnclamped, extendedBody]
    simp only [continuing, if_true]
    rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
    exact targetExecution
  · rw [← extendedCost] at bodyCost
    simp only [comp] at recursiveCost ⊢
    rw [steps_loop_run _ _ _ _ extendedBody continuing (by show targetBody.clock + recursiveClock ≠ 0; omega),
      reentryEq, steps_loop_run _ _ _ _ bodyExecution continuing nonzero]
    exact Nat.add_le_add (Nat.add_le_add_left bodyCost 1) recursiveCost


/-- The raw-call optimization does not increase the steps of a loop. -/
theorem loopWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (body, source) = (r, u) ∧ r ≠ some .error ∧ stateRel i source t →
      SimulationWithin (comp i body) i t u r (steps (body, source)))
    (reentryIH : ∀ (bodyResult : Option (StackSemResult width)) (bodyPost : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (bodyResult, bodyPost) → contLoop bodyResult = true → bodyPost.clock ≠ 0 →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
        evaluate (.loop body, decClock bodyPost) = (r, u) ∧ r ≠ some .error ∧ stateRel i (decClock bodyPost) t →
        SimulationWithin (comp i (.loop body)) i t u r (steps (.loop body, decClock bodyPost)))
    (hypothesis : evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info (.loop body)) info target post result (steps (.loop body, source)) ∧
    SimulationWithin (comp info (.loop body)) info target post result (steps (.loop body, source)) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have bodyNonerror := loopBodyNonError body source post result execution nonerror
  have same : compTop info (.loop body) = comp info (.loop body) := rfl
  rw [same]
  suffices simulation : SimulationWithin (comp info (.loop body)) info target post result
      (steps (.loop body, source)) by exact ⟨simulation, simulation⟩
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  have bodySimulation := bodyIH info target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact loopTimeoutWithinSteps body info source target bodyPost bodyResult bodyExecution continuing zero bodySimulation
    · rw [if_neg zero] at execution
      exact loopReentryWithinSteps body info source target bodyPost post bodyResult result bodyExecution
        continuing zero bodySimulation (reentryIH bodyResult bodyPost bodyExecution continuing zero) execution nonerror
  · have exit : contLoop bodyResult = false := by
      cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact loopExitWithinSteps body info source target bodyPost bodyResult bodyExecution exit bodySimulation

end SteppedFlapjack.StackRawCallSteps
