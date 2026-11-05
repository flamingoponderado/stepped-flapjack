import SteppedFlapjack.StackAllocSteps.AllocCallSteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.AllocStore

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The allocation case of stack allocation preserves execution within a concrete step bound. -/
theorem goalAllocSteps (anything : WordSemGcFun width) (cr : CompileFn width C)
    (s : StackSemStateFiniteExact width C F) (k : Nat) :
    ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width)),
    evaluate (.alloc k, s) = (r, t) → r ≠ some .error → StackProps.allocArg (.alloc k : HolProg width) →
    Pre cr c s regs → ∃ ck regs1,
      evaluate ((comp n m (.alloc k)).1, Tgt anything cr c s ck regs) = (r, Res anything cr c t regs1) ∧
      Post r t regs1 ∧
      steps ((comp n m (.alloc k)).1, Tgt anything cr c s ck regs) ≤
        4 + allocGcStepCost (width := width) c s.stack.length := by
  intro r t m n c regs h hr ha hpre
  have hk : k = 1 := ha
  subst hk
  rw [evaluate_alloc] at h
  simp only [hpre.useAlloc, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i w hw
    have hac := StackPropsAllocationConstants.allocConst w s t r h
    obtain ⟨-, -, -, -, -, hcode, -, -, -, -, hbm, -, hdb, -, hor⟩ := hac
    have h' := alloc_withCompile w s cr (oracleMap ∘ s.compileOracle)
    rw [h] at h'
    have hb := hpre.buf
    obtain ⟨ck, l2, he, hsub, hsteps⟩ := allocCallCorrectStepsBound (c := c) (l := regs) (n' := n) (m := m)
      (anything := anything) h' hr hpre.gcFun
      (by unfold BufBound at hb; show s.bitmaps.length < 2 ^ width - 1; omega)
      hpre.stack (hpre.regs _ _ hw)
    refine ⟨ck, l2, ?_, ⟨hsub, ?_, fun hh => ?_⟩, ?_⟩
    · show evaluate (.call (some (.skip, 0, n, m)) (.inl gcStubLocation) none, _) = _
      convert he using 3
      all_goals first | rfl | rw [hcode] | rw [hor]
    · unfold BufBound at hb ⊢
      rw [hbm, hdb]; exact hb
    · unfold StackBound
      rw [AllocCorrect.alloc_length_stack h hpre.gcFun hh]
      exact hpre.stack
    · change steps (.call (some (.skip, 0, n, m)) (.inl gcStubLocation) none,
        Tgt anything cr c s ck regs) ≤ _
      simpa [Tgt] using hsteps
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

end SteppedFlapjack.StackAllocSteps
