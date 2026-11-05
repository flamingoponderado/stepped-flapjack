import SteppedFlapjack.StackRemoveSteps.OracleRunEffect
/-! Composition of finite oracle effects through source control flow. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open SteppedFlapjack.StackSteps Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

theorem oracleRunEffect_mono {m n : Nat} (s t : StackSemStateFiniteExact width C F)
    (h : oracleRunEffect m s t) (hmn : m ≤ n) : oracleRunEffect n s t := by
  obtain ⟨used, hu, ho, hb⟩ := h
  exact ⟨used, hu.trans hmn, ho, hb⟩

theorem oracleRunEffect_seq (a b : HolProg width) (s middle post : StackSemStateFiniteExact width C F)
    (ha : evaluate (a, s) = (none, middle))
    (iha : oracleRunEffect (steps (a, s)) s middle)
    (ihb : oracleRunEffect (steps (b, middle)) middle post) :
    oracleRunEffect (steps (.seq a b, s)) s post := by
  rw [steps_seq_run a b s middle ha]
  exact oracleRunEffect_mono s post (oracleRunEffect_trans s middle post iha ihb) (by omega)
theorem oracleRunEffect_of_fields (fuel : Nat) (s t : StackSemStateFiniteExact width C F)
    (horacle : t.compileOracle = s.compileOracle) (hbitmap : t.bitmaps = s.bitmaps) :
    oracleRunEffect fuel s t := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · rw [horacle]; funext index; simp [holShiftSeq]
  · simp [hbitmap, oracleBitmapBudget]

theorem oracleRunEffect_decClock (s : StackSemStateFiniteExact width C F) :
    oracleRunEffect 0 s (decClock s) := by
  refine ⟨0, by omega, ?_, ?_⟩
  · funext index; simp [decClock, holShiftSeq]
  · simp [decClock, oracleBitmapBudget]

theorem oracleRunEffect_loop_continue (body : HolProg width)
    (s middle post : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (hbody : evaluate (body, s) = (r, middle)) (hcont : contLoop r = true)
    (hclock : middle.clock ≠ 0)
    (ihbody : oracleRunEffect (steps (body, s)) s middle)
    (ihloop : oracleRunEffect (steps (.loop body, decClock middle)) (decClock middle) post) :
    oracleRunEffect (steps (.loop body, s)) s post := by
  rw [steps_loop_run body s middle r hbody hcont hclock]
  have hfirst := oracleRunEffect_trans s middle (decClock middle) ihbody (oracleRunEffect_decClock middle)
  have hboth := oracleRunEffect_trans s (decClock middle) post hfirst ihloop
  exact oracleRunEffect_mono s post hboth (by omega)
theorem oracleRunEffect_ite_true (cmp : Cmp) (reg : Nat) (ri : HolRegImm width)
    (a b : HolProg width) (s post : StackSemStateFiniteExact width C F)
    (x y : WordLocW width) (hx : getVar reg s = some x)
    (hy : getVarImm (HolRegImm.toWordRegImm ri) s = some y)
    (hw : wordSemWordCmp cmp x y = some true)
    (ih : oracleRunEffect (steps (a, s)) s post) :
    oracleRunEffect (steps (.ite cmp reg ri a b, s)) s post := by
  rw [steps_ite_true cmp reg ri a b s x y hx hy hw]
  exact oracleRunEffect_mono s post ih (by omega)

theorem oracleRunEffect_ite_false (cmp : Cmp) (reg : Nat) (ri : HolRegImm width)
    (a b : HolProg width) (s post : StackSemStateFiniteExact width C F)
    (x y : WordLocW width) (hx : getVar reg s = some x)
    (hy : getVarImm (HolRegImm.toWordRegImm ri) s = some y)
    (hw : wordSemWordCmp cmp x y = some false)
    (ih : oracleRunEffect (steps (b, s)) s post) :
    oracleRunEffect (steps (.ite cmp reg ri a b, s)) s post := by
  rw [steps_ite_false cmp reg ri a b s x y hx hy hw]
  exact oracleRunEffect_mono s post ih (by omega)
end SteppedFlapjack.StackRemoveSteps.CompCorrect
