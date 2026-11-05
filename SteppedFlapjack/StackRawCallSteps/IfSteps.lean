import SteppedFlapjack.StackRawCallSteps.LeafSteps
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open SteppedFlapjack.StackSteps

/-- The conditional case preserves a nonincreasing bound for the chosen branch. -/
theorem ifWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : HolRegImm width) (first second : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (first, source) = (r, u) ∧ r ≠ some .error ∧ stateRel i source t →
      SimulationWithin (comp i first) i t u r (steps (first, source)))
    (secondIH : ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (second, source) = (r, u) ∧ r ≠ some .error ∧ stateRel i source t →
      SimulationWithin (comp i second) i t u r (steps (second, source)))
    (h : evaluate (.ite cmp reg operand first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info (.ite cmp reg operand first second)) info target post result
        (steps (.ite cmp reg operand first second, source)) ∧
    SimulationWithin (comp info (.ite cmp reg operand first second)) info target post result
        (steps (.ite cmp reg operand first second, source)) := by
  obtain ⟨execution, nonerror, relation⟩ := h
  have same : compTop info (.ite cmp reg operand first second) =
      comp info (.ite cmp reg operand first second) := rfl
  rw [same]
  suffices simulation : SimulationWithin (comp info (.ite cmp reg operand first second))
      info target post result (steps (.ite cmp reg operand first second, source)) by
    exact ⟨simulation, simulation⟩
  rw [evaluate_ite] at execution
  split at execution
  · rename_i left right leftRead rightRead
    split at execution
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ :=
        firstIH info target post result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateCompiledIf info source target relation]
        simp_all
      · simp only [comp]
        rw [steps_ite, steps_ite]
        rw [getVar_targetClock info source target relation,
          getVarImm_targetClock info source target relation]
        simp only [leftRead, rightRead, compared]
        omega
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ :=
        secondIH info target post result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateCompiledIf info source target relation]
        simp_all
      · simp only [comp]
        rw [steps_ite, steps_ite]
        rw [getVar_targetClock info source target relation,
          getVarImm_targetClock info source target relation]
        simp only [leftRead, rightRead, compared]
        omega
    · simp_all
  · simp_all
end SteppedFlapjack.StackRawCallSteps
