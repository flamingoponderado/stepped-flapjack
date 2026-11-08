import SteppedFlapjack.CrepSteps.Defs
namespace SteppedFlapjack.CrepSteps
open Flapjack Flapjack.Basis.Pure.MlString

/-- Result and local-state behavior of a zero-argument tail call. -/
def tailExit {width : Nat} [NeZero width] {σ : Type}
    (result : Option (CrepResultHOLExact width)) (final : CrepSemHOLState width σ) :
    Option (CrepResultHOLExact width) × CrepSemHOLState width σ :=
  match result with
  | none | some (.break _) | some (.continue _) => (some .error,final)
  | some result => (some result,final.emptyLocals)

/-- A zero-argument tail wrapper adds at most three evaluator visits. -/
theorem tail_entry {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : MlString) (body : CrepProgHOL width)
    (result : Option (CrepResultHOLExact width)) (final : CrepSemHOLState width σ) (limit : Nat)
    (lookup : state.code.lookup name = some ([],body)) (nonzero : state.clock ≠ 0)
    (run : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) body = (result,final))
    (bound : steps body (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) ≤ limit) :
    evalCrepSemHOLProgExact state (.seq .skip (.call none name [])) = tailExit result final ∧
    steps (.seq .skip (.call none name [])) state ≤ 3 + limit := by
  constructor
  · rw [evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
    simp only [if_true]
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp [lookupCodeFiniteHOL,lookup,crepReturnInfoNodupError,nonzero,decClockCrepSemHOL] at run ⊢
    rw [run]
    cases result with
    | none => rfl
    | some result => cases result <;> rfl
  · rw [steps_seq]
    simp only [evalCrepSemHOLProgExact_skip]
    rw [steps_call_tail name [] _ [] [] _ (by simp) lookup (by simp) (by simp) nonzero]
    have one : steps (.skip : CrepProgHOL width) state = 1 := steps_leaf _ _ rfl
    rw [one]
    simp only [List.zip, List.zipWith] at bound ⊢
    omega
end SteppedFlapjack.CrepSteps
