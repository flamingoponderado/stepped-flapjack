import SteppedFlapjack.StackRemoveSteps.InstallEffect
/-! Composable bounds on the oracle entries and bitmap words consumed by runs. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
variable {width : Nat} [NeZero width] {C F : Type}

/-- A transition consuming at most `fuel` oracle entries and their bitmap data. -/
def oracleRunEffect (fuel : Nat) (s t : StackSemStateFiniteExact width C F) : Prop :=
  ∃ used ≤ fuel, t.compileOracle = holShiftSeq used s.compileOracle ∧
    t.bitmaps.length ≤ s.bitmaps.length + oracleBitmapBudget used s.compileOracle

theorem oracleRunEffect_refl (fuel : Nat) (s : StackSemStateFiniteExact width C F) :
    oracleRunEffect fuel s s := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · funext index; simp [holShiftSeq]
  · simp [oracleBitmapBudget]

theorem oracleRunEffect_trans {a b : Nat} (s t u : StackSemStateFiniteExact width C F)
    (h1 : oracleRunEffect a s t) (h2 : oracleRunEffect b t u) :
    oracleRunEffect (a + b) s u := by
  obtain ⟨x, hx, ho1, hb1⟩ := h1
  obtain ⟨y, hy, ho2, hb2⟩ := h2
  refine ⟨x + y, by omega, ?_, ?_⟩
  · rw [ho2, ho1]
    funext index
    simp only [holShiftSeq]
    congr 1
    omega
  · rw [ho1] at hb2
    have hbudget := oracleBitmapBudget_add x y s.compileOracle
    omega

theorem oracleRunEffect_install (ptr len dptr dlen ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.install ptr len dptr dlen ret : HolProg width), s) = (r, t)) :
    oracleRunEffect 1 s t := by
  rcases evaluate_install_effect ptr len dptr dlen ret s t r h with same | installed
  · rcases same with ⟨_, ho, hb⟩
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [ho]; funext i; simp [holShiftSeq]
    · simp [hb, oracleBitmapBudget]
  · rcases installed with ⟨_, ho, hb⟩
    refine ⟨1, by omega, ho, ?_⟩
    simp [hb, oracleBitmapBudget]
/-- A run effect carries the initial finite-prefix bounds to the remaining prefix. -/
theorem oracleRunEffect_prefix {B K n : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F) (h : oracleRunEffect n s t)
    (ho : oraclePrefixBound B bounds K n s)
    (hb : s.bitmaps.length + oracleBitmapBudget n s.compileOracle ≤ B) :
    ∃ used ≤ n, oraclePrefixBound B bounds K (n - used) t ∧
      t.bitmaps.length + oracleBitmapBudget (n - used) t.compileOracle ≤ B := by
  obtain ⟨used, hused, horacle, hbitmap⟩ := h
  exact ⟨used, hused, oraclePrefixBound_drop s t ho hused horacle,
    oracleBitmapBudget_drop s t hused horacle hbitmap hb⟩

end SteppedFlapjack.StackRemoveSteps.CompCorrect
