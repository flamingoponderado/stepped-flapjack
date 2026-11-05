import SteppedFlapjack.StackRawCallSteps.CallTailSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Return
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open SteppedFlapjack.StackSteps

/-- A returning call's reached callee is simulated with its step bound, while
the frame information of the outer program is restored. -/
theorem returningCalleeWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (link l1 l2 : Nat) (info : Spt Nat)
    (source target middle : StackSemStateFiniteExact width C F)
    (program : HolProg width) (result : Option (StackSemResult width))
    (calleeIH : ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 → ∀ (i : Spt Nat) (t u : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, u) ∧
        r ≠ some .error ∧ stateRel i (decClock (setVar link (.loc l1 l2) source)) t →
      SimulationWithin (compTop i program) i t u r (steps (program, decClock (setVar link (.loc l1 l2) source))))
    (relation : stateRel info source target)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (execution : evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle))
    (nonerror : result ≠ some .error) :
    ∃ entryInfo, findCode dest (target.regs.eraseEq link) target.code = some (compTop entryInfo program) ∧
      SimulationWithin (compTop entryInfo program) info (decClock (setVar link (.loc l1 l2) target))
        middle result (steps (program, decClock (setVar link (.loc l1 l2) source))) := by
  obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
    callEntryErased info source target relation dest link program lookup
  obtain ⟨clock, targetMiddle, space, middleRelation, targetExecution, guard, cost⟩ :=
    calleeIH program lookup nonzero entryInfo (decClock (setVar link (.loc l1 l2) target)) middle result
      ⟨execution, nonerror, LoopCase.stateRel_decClock entryInfo
        (setVar link (.loc l1 l2) source) (setVar link (.loc l1 l2) target)
        (stateRel_setVar entryInfo source target entryRelation link (.loc l1 l2))⟩
  have frames : stateOk info source.code := by
    obtain ⟨_, _, _, frames, _⟩ := relation
    exact frames
  have middleFrames := stateOk_afterEvaluate info program
    (decClock (setVar link (.loc l1 l2) source)) middle result frames execution
  exact ⟨entryInfo, targetLookup, clock, targetMiddle, space,
    stateRel_changeInfo entryInfo info middle targetMiddle middleRelation middleFrames,
    targetExecution, guard, cost⟩
end SteppedFlapjack.StackRawCallSteps
