import SteppedFlapjack.StackRemoveSteps.CodeOriginEvaluate
/-! Preservation of finite code, oracle and bitmap budgets across a subrun. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- An actual subrun preserves a finite code/oracle/bitmap budget and records
how many oracle entries it consumed. -/
theorem runBudget_after {B K n : Nat} {bounds : BitVec width × BitVec width}
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (hsteps : steps (p, s) ≤ n) (hcode : codeBound B bounds K s)
    (horacle : oraclePrefixBound B bounds K n s)
    (hbitmap : s.bitmaps.length + oracleBitmapBudget n s.compileOracle ≤ B) :
    ∃ used ≤ steps (p, s), codeBound B bounds K t ∧
      oraclePrefixBound B bounds K (n - used) t ∧
      t.bitmaps.length + oracleBitmapBudget (n - used) t.compileOracle ≤ B := by
  have he := oracleRunEffect_evaluate p s t r h
  obtain ⟨used, hused, hshift, hb⟩ := he
  have hun : used ≤ n := hused.trans hsteps
  refine ⟨used, hused, ?_, ?_, ?_⟩
  · exact codeOrigin_bound s t (codeOrigin_evaluate p s t r h) hsteps hcode horacle
  · exact oraclePrefixBound_drop s t horacle hun hshift
  · exact oracleBitmapBudget_drop s t hun hshift hb hbitmap
/-- A shorter remaining prefix never needs a larger bitmap budget. -/
theorem oracleBitmapBudget_mono {n m : Nat}
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hmn : m ≤ n) : oracleBitmapBudget m oracle ≤ oracleBitmapBudget n oracle := by
  have hn : m + (n - m) = n := by omega
  have h := oracleBitmapBudget_add m (n - m) oracle
  rw [hn] at h
  omega

theorem runBudget_weaken {B K n m : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F) (hmn : m ≤ n)
    (horacle : oraclePrefixBound B bounds K n s)
    (hbitmap : s.bitmaps.length + oracleBitmapBudget n s.compileOracle ≤ B) :
    oraclePrefixBound B bounds K m s ∧
      s.bitmaps.length + oracleBitmapBudget m s.compileOracle ≤ B := by
  refine ⟨oraclePrefixBound_take s horacle hmn, ?_⟩
  have hb := oracleBitmapBudget_mono s.compileOracle hmn
  omega

/-- Code, oracle and bitmap budgets transfer across unrelated state updates. -/
theorem runBudget_congr {B K n : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F)
    (hcode : t.code = s.code) (horacle : t.compileOracle = s.compileOracle)
    (hbitmap : t.bitmaps = s.bitmaps)
    (hc : codeBound B bounds K s) (ho : oraclePrefixBound B bounds K n s)
    (hb : s.bitmaps.length + oracleBitmapBudget n s.compileOracle ≤ B) :
    codeBound B bounds K t ∧ oraclePrefixBound B bounds K n t ∧
      t.bitmaps.length + oracleBitmapBudget n t.compileOracle ≤ B := by
  refine ⟨codeBound_congr hcode hc, ?_, ?_⟩
  · intro index hi name program hm
    rw [horacle] at hm
    exact ho index hi name program hm
  · simpa only [horacle, hbitmap] using hb

theorem steps_seq_first_le (a b : HolProg width) (s : StackSemStateFiniteExact width C F) :
    steps (a, s) ≤ steps (.seq a b, s) := by
  rw [steps_seq]
  exact (Nat.le_add_left (steps (a, s)) 1).trans (Nat.le_add_right _ _)

theorem steps_loop_body_le (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    steps (body, s) ≤ steps (.loop body, s) := by
  rw [steps_loop]
  exact (Nat.le_add_left (steps (body, s)) 1).trans (Nat.le_add_right _ _)

end SteppedFlapjack.StackRemoveSteps.CompCorrect
