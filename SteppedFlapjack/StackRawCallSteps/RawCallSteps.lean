import SteppedFlapjack.StackRawCallSteps.SeqSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.IfCase
open SteppedFlapjack.StackSteps

/-- Existing raw calls preserve the nonincreasing bound of the reached body. -/
theorem rawCallWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ∀ (first body : HolProg width), sptLookup dest source.code = some (.seq first body) →
      source.clock ≠ 0 → ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (body, decClock source) = (r, u) ∧ r ≠ some .error ∧ stateRel i (decClock source) t →
      SimulationWithin (comp i body) i t u r (steps (body, decClock source)))
    (hypothesis : evaluate (.rawCall dest, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info (.rawCall dest)) info target resultState result (steps (.rawCall dest, source)) ∧
    SimulationWithin (comp info (.rawCall dest)) info target resultState result (steps (.rawCall dest, source)) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change SimulationWithin (.rawCall dest) info target resultState result (steps (.rawCall dest, source)) ∧
    SimulationWithin (.rawCall dest) info target resultState result (steps (.rawCall dest, source))
  suffices simulation : SimulationWithin (.rawCall dest) info target resultState result (steps (.rawCall dest, source)) by
    exact ⟨simulation, simulation⟩
  rw [evaluate_rawCall] at execution
  cases lookup : sptLookup dest source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases program <;> simp only [destSeq] at execution
    all_goals try (exact False.elim (nonerror (Prod.mk.inj execution).1.symm))
    rename_i first body
    obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
      rawCallEntry info source target relation dest first body lookup
    have clockEq := LoopCase.stateRel_clock info source target relation
    by_cases zero : source.clock = 0
    · simp only [zero, if_true, Prod.mk.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
        LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_, ?_⟩
      · simp only [Nat.add_zero, evaluate_rawCall, targetLookup, destSeq]
        have tz : target.clock = 0 := clockEq.trans zero
        simp only [tz, if_true]
        have update : { target with clock := 0 } = target := by rw [← tz]
        rw [update]
      · simp
      · rw [steps_rawCall, steps_rawCall]
        simp [targetLookup, lookup, destSeq, clockEq, zero]
    · simp only [zero, if_false] at execution
      rcases bodyExecution : evaluate (body, decClock source) with ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror, LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluate info body (decClock source) bodyPost bodyResult frames bodyExecution
        refine ⟨clock, targetState, stackSpace,
          stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames, ?_, guard, ?_⟩
        · have targetNonzero : target.clock ≠ 0 := by omega
          have addedNonzero : target.clock + clock ≠ 0 := by omega
          simp only [evaluate_rawCall, targetLookup, destSeq, addedNonzero, if_false,
            StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
            targetExecution, bad, Bool.false_eq_true, if_false]
        · have targetNonzero : target.clock ≠ 0 := by omega
          have addedNonzero : target.clock + clock ≠ 0 := by omega
          rw [steps_rawCall, steps_rawCall]
          simp only [targetLookup, lookup, destSeq, addedNonzero, zero, if_false,
            StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero]
          exact Nat.add_le_add_left cost 1
end SteppedFlapjack.StackRawCallSteps
