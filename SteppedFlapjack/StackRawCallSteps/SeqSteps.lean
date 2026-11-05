import SteppedFlapjack.StackRawCallSteps.SeqOptimizedSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open SteppedFlapjack.StackSteps

/-- Raw-call optimization does not increase a sequence's counted steps. -/
theorem seqWithinSteps {width : Nat} [NeZero width] {C F : Type}
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
    SimulationWithin (compTop info (.seq first second)) info target post result (steps (.seq first second, source)) ∧
    SimulationWithin (comp info (.seq first second)) info target post result (steps (.seq first second, source)) := by
  have standard := standardSeqWithinSteps first second info source target post result firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change SimulationWithin (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result (steps (.seq first second, source))
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
          simpa only [compSeq, destCase, frame] using
            optimizedSeqWithinSteps released allocated dest info source target post result frame secondIH hypothesis
end SteppedFlapjack.StackRawCallSteps
