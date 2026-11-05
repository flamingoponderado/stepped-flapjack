import SteppedFlapjack.StackRawCallSteps.CallReturnSupport
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open SteppedFlapjack.StackSteps
theorem callReturnWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program → source.clock ≠ 0 →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, u) ∧
        r ≠ some .error ∧ stateRel i (decClock (setVar link (.loc l1 l2) source)) t →
      SimulationWithin (compTop i program) i t u r (steps (program, decClock (setVar link (.loc l1 l2) source))))
    (returnIH : ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program → source.clock ≠ 0 →
      ∀ middle, evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), middle) →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (ret, middle) = (r, u) ∧ r ≠ some .error ∧ stateRel i middle t →
      SimulationWithin (comp i ret) i t u r (steps (ret, middle)))
    (exceptionIH : ∀ program h hl1 hl2, findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 → handler = some (h, hl1, hl2) → ∀ middle,
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (h, middle) = (r, u) ∧ r ≠ some .error ∧ stateRel i middle t →
      SimulationWithin (comp i h) i t u r (steps (h, middle)))
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result (steps (.call (some (ret, link, l1, l2)) dest handler, source)) ∧
    SimulationWithin (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result (steps (.call (some (ret, link, l1, l2)) dest handler, source)) := by
  classical
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  suffices simulation :
      SimulationWithin (comp info (.call (some (ret, link, l1, l2)) dest handler))
        info target post result (steps (.call (some (ret, link, l1, l2)) dest handler, source)) by
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  cases lookup : findCode dest (source.regs.eraseEq link) source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      have clockEq := LoopCase.stateRel_clock info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨entryInfo, _, targetLookup⟩ :=
          callEntryErased info source target relation dest link program lookup
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
          LoopCase.stateRel_emptyEnv info source target relation, ?_, by simp, ?_⟩
        · have targetZero : target.clock = 0 := clockEq.trans zero
          have update : {target with clock := 0} = target := by rw [← targetZero]
          cases handler with
          | none =>
              simp only [comp, Nat.add_zero, targetZero, update,
                StackSemEvaluate.evaluate_call, targetLookup, if_true]
          | some triple =>
              obtain ⟨h, hl1, hl2⟩ := triple
              simp only [comp, Nat.add_zero, targetZero, update,
                StackSemEvaluate.evaluate_call, targetLookup, if_true]
        · cases handler with
          | none => simp [comp, steps_call_some, targetLookup, lookup, clockEq, zero]
          | some triple =>
              obtain ⟨h, hl1, hl2⟩ := triple
              simp [comp, steps_call_some, targetLookup, lookup, clockEq, zero]
      · simp only [zero, if_false] at execution
        rw [StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate
          (program, decClock (setVar link (.loc l1 l2) source)) with
          ⟨bodyResult, middle⟩
        rw [bodyExecution] at execution
        have bodyNonerror : bodyResult ≠ some .error := by
          intro equal
          rw [equal] at execution
          simp only [Prod.mk.injEq] at execution
          exact nonerror execution.1.symm
        obtain ⟨entryInfo, targetLookup, firstClock, targetMiddle, firstSpace,
          middleRelation, calleeExecution, firstGuard, calleeCost⟩ :=
          returningCalleeWithinSteps dest link l1 l2 info source target middle program bodyResult
            calleeIH relation lookup zero bodyExecution bodyNonerror
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + firstClock ≠ 0 := by omega
        have calleeNative : StackSemEvaluate.evaluate
            (compTop entryInfo program, decClock (setVar link (.loc l1 l2)
              {target with clock := target.clock + firstClock})) =
            (bodyResult, {targetMiddle with stackSpace := firstSpace}) := by
          rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
          exact calleeExecution
        cases bodyResult with
        | none =>
            simp only [Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
        | some value =>
            cases value with
            | error => exact False.elim (bodyNonerror rfl)
            | «break» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | «continue» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | halt value =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · cases handler with
                  | none =>
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
            | timeOut =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · cases handler with
                  | none =>
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
            | finalFFI event =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · cases handler with
                  | none =>
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
            | result value =>
                by_cases equal : value = .loc l1 l2
                · subst value
                  simp only [ne_eq, not_true_eq_false, if_false] at execution
                  have spaceEq := firstGuard (by simp)
                  subst firstSpace
                  have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                      targetMiddle := by cases targetMiddle; rfl
                  rw [selfSpace] at calleeExecution
                  obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                    continuationExecution, finalGuard, continuationCost⟩ :=
                    returnIH program lookup zero middle bodyExecution info targetMiddle post result
                      ⟨execution, nonerror, middleRelation⟩
                  have extended := extendReturningCallee (compTop entryInfo program) target
                    targetMiddle (some (.result (.loc l1 l2))) link l1 l2 firstClock secondClock
                    targetNonzero calleeExecution (by simp)
                  have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                  refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard, ?_⟩
                  · cases handler with
                    | none =>
                        simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                    | some triple =>
                        obtain ⟨h, hl1, hl2⟩ := triple
                        simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                  · have extendedCost : steps (compTop entryInfo program,
                        decClock (setVar link (.loc l1 l2) {target with clock := target.clock + (firstClock + secondClock)})) =
                        steps (compTop entryInfo program, {decClock (setVar link (.loc l1 l2) target) with
                          clock := (decClock (setVar link (.loc l1 l2) target)).clock + firstClock}) := by
                      rw [returningInput_addClock target link l1 l2 (firstClock + secondClock) targetNonzero]
                      simpa only [Nat.add_assoc] using steps_addClock secondClock _ _ _ rfl
                        (some (.result (.loc l1 l2))) targetMiddle calleeExecution (by simp)
                    cases handler with
                    | none =>
                        simp only [comp, steps_call_some, targetLookup, lookup, totalNonzero, zero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended,
                          StackSemEvaluateClock.fixClockEvaluate, bodyExecution]
                        simp only [if_true]
                        rw [extendedCost]
                        exact Nat.add_le_add_left (Nat.add_le_add calleeCost continuationCost) 1
                    | some triple =>
                        obtain ⟨h, hl1, hl2⟩ := triple
                        simp only [comp, steps_call_some, targetLookup, lookup, totalNonzero, zero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended,
                          StackSemEvaluateClock.fixClockEvaluate, bodyExecution]
                        simp only [if_true]
                        rw [extendedCost]
                        exact Nat.add_le_add_left (Nat.add_le_add calleeCost continuationCost) 1
                · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                  exact False.elim (nonerror execution.1.symm)
            | exception value =>
                cases handler with
                | none =>
                    simp only [Prod.mk.injEq] at execution
                    obtain ⟨rfl, rfl⟩ := execution
                    refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                    · simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                    · simp only [comp, steps_call_some, targetLookup, lookup, addedNonzero, zero, if_false,
                        calleeNative, bodyExecution]
                      rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                      exact Nat.add_le_add_left calleeCost 1
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    by_cases equal : value = .loc hl1 hl2
                    · subst value
                      simp only [ne_eq, not_true_eq_false, if_false] at execution
                      have spaceEq := firstGuard (by simp)
                      subst firstSpace
                      have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                          targetMiddle := by cases targetMiddle; rfl
                      rw [selfSpace] at calleeExecution
                      obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                        continuationExecution, finalGuard, continuationCost⟩ :=
                        exceptionIH program h hl1 hl2 lookup zero rfl middle bodyExecution
                          info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
                      have extended := extendReturningCallee (compTop entryInfo program) target
                        targetMiddle (some (.exception (.loc hl1 hl2))) link l1 l2
                        firstClock secondClock targetNonzero calleeExecution (by simp)
                      have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                      refine ⟨firstClock + secondClock, targetPost, finalSpace,
                        postRelation, ?_, finalGuard, ?_⟩
                      · simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                      · have extendedCost : steps (compTop entryInfo program,
                            decClock (setVar link (.loc l1 l2) {target with clock := target.clock + (firstClock + secondClock)})) =
                            steps (compTop entryInfo program, {decClock (setVar link (.loc l1 l2) target) with
                              clock := (decClock (setVar link (.loc l1 l2) target)).clock + firstClock}) := by
                          rw [returningInput_addClock target link l1 l2 (firstClock + secondClock) targetNonzero]
                          simpa only [Nat.add_assoc] using steps_addClock secondClock _ _ _ rfl
                            (some (.exception (.loc hl1 hl2))) targetMiddle calleeExecution (by simp)
                        simp only [comp, steps_call_some, targetLookup, lookup, totalNonzero, zero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended,
                          StackSemEvaluateClock.fixClockEvaluate, bodyExecution]
                        simp only [if_true]
                        rw [extendedCost]
                        exact Nat.add_le_add_left (Nat.add_le_add calleeCost continuationCost) 1
                    · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                      exact False.elim (nonerror execution.1.symm)
end SteppedFlapjack.StackRawCallSteps
