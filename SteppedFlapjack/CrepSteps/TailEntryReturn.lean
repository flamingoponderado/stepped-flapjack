import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop

/-! Invert a successful generated zero-argument entry. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack Flapjack.Basis.Pure.MlString

/-- A returning entry comes from a returning callee, whose visits are bounded
by those of the entry. -/
theorem tail_entry_return_inv {width : Nat} [NeZero width] {σ : Type}
    (state final : CrepSemHOLState width σ) (name : MlString) (body : CrepProgHOL width)
    (values : List (HolWordLab width)) (limit : Nat)
    (lookup : state.code.lookup name = some ([],body)) (nonzero : state.clock ≠ 0)
    (run : evalCrepSemHOLProgExact state (.seq .skip (.call none name [])) = (some (.return values),final))
    (bound : steps (.seq .skip (.call none name [])) state ≤ limit) :
    ∃ calleeFinal,
      evalCrepSemHOLProgExact (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) body =
        (some (.return values),calleeFinal) ∧
      steps body (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) ≤ limit := by
  let entry := decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}
  rcases callee : evalCrepSemHOLProgExact entry body with ⟨r,post⟩
  have wrapper := (tail_entry state name body r post (steps body entry) lookup nonzero callee le_rfl).1
  rw [run] at wrapper
  have resultEq : r = some (.return values) := by
    cases r with
    | none => simp [tailExit] at wrapper
    | some r => cases r <;> simp_all [tailExit]
  have count := SteppedFlapjack.CrepToLoopSteps.tailEntry_callee_steps_le .skip name body state state
    (by rw [evalCrepSemHOLProgExact_skip]) lookup nonzero
  refine ⟨post,?_,count.trans bound⟩
  simp [entry,resultEq] at callee ⊢
end SteppedFlapjack.CrepSteps
