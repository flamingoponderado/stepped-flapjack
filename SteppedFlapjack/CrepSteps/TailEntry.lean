import SteppedFlapjack.CrepSteps.Defs

/-! A generated entry wrapper delegates its run and bound to its callee. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack Flapjack.Basis.Pure.MlString

/-- A zero-argument tail wrapper adds three evaluator visits to a returning
callee. The code lookup and callee run are actual execution facts. -/
theorem tail_entry_returned_word {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : MlString) (body : CrepProgHOL width)
    (word : BitVec width) (final : CrepSemHOLState width σ) (limit : Nat)
    (lookup : state.code.lookup name = some ([],body)) (nonzero : state.clock ≠ 0)
    (run : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) body =
        (some (.return [.word word]),final))
    (bound : steps body (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) ≤ limit) :
    evalCrepSemHOLProgExact state (.seq .skip (.call none name [])) =
      (some (.return [.word word]),final.emptyLocals) ∧
    steps (.seq .skip (.call none name [])) state ≤ 3 + limit := by
  constructor
  · rw [evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
    simp only [if_true]
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp [lookupCodeFiniteHOL,lookup,crepReturnInfoNodupError,nonzero,decClockCrepSemHOL] at run ⊢
    rw [run]
  · rw [steps_seq]
    simp only [evalCrepSemHOLProgExact_skip]
    rw [steps_call_tail name [] _ [] [] _ (by simp) lookup (by simp) (by simp) nonzero]
    have one : steps (.skip : CrepProgHOL width) state = 1 := steps_leaf _ _ rfl
    rw [one]
    simp only [List.zip, List.zipWith] at bound ⊢
    omega

end SteppedFlapjack.CrepSteps
