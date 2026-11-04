import SteppedFlapjack.StepPreservation.Basic

/-! Compile-time checks of the step-preservation framework. -/

namespace SteppedFlapjack.Test.StepPreservation

open SteppedFlapjack.StepPreservation

-- `outer.comp inner` applies `inner` first: 2 * (4 * n + 5) + 3 = 8 * n + 13.
example : LinearBound.comp ⟨2, 3⟩ ⟨4, 5⟩ = ⟨8, 13⟩ := by decide
#guard (LinearBound.comp ⟨2, 3⟩ ⟨4, 5⟩).apply 10 = (LinearBound.mk 2 3).apply ((LinearBound.mk 4 5).apply 10)
#guard LinearBound.id.apply 7 = 7

-- Composing two step-preserving "passes" on `Nat` states: the source finishes
-- in `s` steps, the middle pass doubles them, the last adds one.
example : StepPreserving (fun (s : Nat) n => s ≤ n) (fun (t : Nat) n => t ≤ n)
    (fun s t => t ≤ 2 * s + 1) (LinearBound.comp ⟨1, 1⟩ ⟨2, 0⟩) := by
  have h1 : StepPreserving (fun (s : Nat) n => s ≤ n) (fun (m : Nat) n => m ≤ n)
      (fun s m => m ≤ 2 * s) ⟨2, 0⟩ := by
    intro s m n hsm hs; simp only [LinearBound.apply]; omega
  have h2 : StepPreserving (fun (m : Nat) n => m ≤ n) (fun (t : Nat) n => t ≤ n)
      (fun m t => t ≤ m + 1) ⟨1, 1⟩ := by
    intro m t n hmt hm; simp only [LinearBound.apply]; omega
  intro s t n hst hs
  exact (StepPreserving.trans h1 h2) s t n ⟨2 * s, Nat.le_refl _, by omega⟩ hs

end SteppedFlapjack.Test.StepPreservation
