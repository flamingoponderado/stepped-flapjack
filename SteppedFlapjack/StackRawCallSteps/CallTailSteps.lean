import SteppedFlapjack.StackRawCallSteps.JumpSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open SteppedFlapjack.StackSteps
theorem callTailWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : handler = none → ∀ (program : HolProg width),
      findCode dest source.regs source.code = some program → source.clock ≠ 0 →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (program, decClock source) = (r, u) ∧ r ≠ some .error ∧ stateRel i (decClock source) t →
      SimulationWithin (compTop i program) i t u r (steps (program, decClock source)))
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info (.call none dest handler)) info target post result (steps (.call none dest handler, source)) ∧
    SimulationWithin (comp info (.call none dest handler)) info target post result (steps (.call none dest handler, source)) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change SimulationWithin (.call none dest handler) info target post result (steps (.call none dest handler, source)) ∧
    SimulationWithin (.call none dest handler) info target post result (steps (.call none dest handler, source))
  suffices simulation : SimulationWithin (.call none dest handler) info target post result (steps (.call none dest handler, source)) by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode dest source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      cases handler with
      | some handler =>
          simp only [Prod.mk.injEq] at execution
          exact False.elim (nonerror execution.1.symm)
      | none =>
          obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
            callEntry info source target relation dest program lookup
          have clockEq := LoopCase.stateRel_clock info source target relation
          by_cases zero : source.clock = 0
          · simp only [zero, if_true, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
              LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_, ?_⟩
            · have targetZero : target.clock = 0 := clockEq.trans zero
              simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup,
                targetZero, if_true]
              have update : {target with clock := 0} = target := by rw [← targetZero]
              rw [update]
            · simp
            · rw [steps_call_none, steps_call_none]
              simp [targetLookup, lookup, clockEq, zero]
          · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
            rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
              ⟨bodyResult, bodyPost⟩
            rw [bodyExecution] at execution
            by_cases bad : badFunReturn bodyResult = true
            · simp only [bad, if_true, Prod.mk.injEq] at execution
              exact False.elim (nonerror execution.1.symm)
            · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
              obtain ⟨rfl, rfl⟩ := execution
              obtain ⟨clock, targetPost, space, postRelation, targetExecution, guard, cost⟩ :=
                calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
                  ⟨bodyExecution, nonerror,
                    LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
              have frames : stateOk info source.code := by
                obtain ⟨_, _, _, frames, _⟩ := relation
                exact frames
              have postFrames := stateOk_afterEvaluate info program (decClock source)
                bodyPost bodyResult frames bodyExecution
              refine ⟨clock, targetPost, space,
                stateRel_changeInfo entryInfo info bodyPost targetPost postRelation postFrames,
                ?_, guard, ?_⟩
              · have targetNonzero : target.clock ≠ 0 := by omega
                have addedNonzero : target.clock + clock ≠ 0 := by omega
                rw [StackSemEvaluate.evaluate_call]
                simp only [targetLookup, addedNonzero, if_false]
                rw [StackSemEvaluateClock.fixClockEvaluate]
                simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                  targetExecution, bad, Bool.false_eq_true, if_false]
              · have targetNonzero : target.clock ≠ 0 := by omega
                have addedNonzero : target.clock + clock ≠ 0 := by omega
                rw [steps_call_none, steps_call_none]
                simp only [targetLookup, lookup, addedNonzero, zero, if_false,
                  StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero]
                exact Nat.add_le_add_left cost 1

end SteppedFlapjack.StackRawCallSteps
