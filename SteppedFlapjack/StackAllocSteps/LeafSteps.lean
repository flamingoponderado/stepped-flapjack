import SteppedFlapjack.StackAllocSteps.StoreConstsSteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps

/-- An unchanged leaf uses exactly one target step and preserves semantics. -/
theorem unchangedLeafSteps {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C) (p : HolProg width)
    (s : StackSemStateFiniteExact width C F) (hleaf : isRecursive p = false)
    (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width))
    (hcomp : (comp n m p).1 = p) (h : evaluate (p, s) = (r, t))
    (hr : r ≠ some .error) (ha : StackProps.allocArg p) (hpre : Pre cr c s regs) :
    ∃ ck regs1,
      evaluate ((comp n m p).1, Tgt anything cr c s ck regs) = (r, Res anything cr c t regs1) ∧
      Post r t regs1 ∧ steps ((comp n m p).1, Tgt anything cr c s ck regs) = 1 := by
  obtain ⟨ck, regs1, he, hp⟩ := goal_all anything cr _ p s rfl r t m n c regs h hr ha hpre
  refine ⟨ck, regs1, he, hp, ?_⟩
  rw [hcomp]
  exact steps_leaf p _ hleaf

/-- Every nonrecursive source statement has a concrete target step bound. -/
theorem leafSteps {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C) (p : HolProg width)
    (s : StackSemStateFiniteExact width C F) (hleaf : isRecursive p = false)
    (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width))
    (h : evaluate (p, s) = (r, t)) (hr : r ≠ some .error)
    (ha : StackProps.allocArg p) (hpre : Pre cr c s regs) :
    ∃ ck regs1,
      evaluate ((comp n m p).1, Tgt anything cr c s ck regs) = (r, Res anything cr c t regs1) ∧
      Post r t regs1 ∧ steps ((comp n m p).1, Tgt anything cr c s ck regs) ≤
        max 5 (4 + allocGcStepCost (width := width) c s.stack.length) := by
  cases p <;> simp only [isRecursive, Bool.true_eq_false] at hleaf
  all_goals first
    | contradiction
    | (obtain ⟨ck, rs, he, hp, hs⟩ := goalAllocSteps anything cr s _ r t m n c regs h hr ha hpre
       exact ⟨ck, rs, he, hp, hs.trans (Nat.le_max_right _ _)⟩)
    | (obtain ⟨ck, rs, he, hp, hs⟩ := goalStoreConstsSteps anything cr s _ _ _ r t m n c regs h hr ha hpre
       exact ⟨ck, rs, he, hp, hs.trans (Nat.le_max_left _ _)⟩)
    | (obtain ⟨ck, rs, he, hp, hs⟩ := unchangedLeafSteps anything cr _ s (by rfl) r t m n c regs rfl h hr ha hpre
       refine ⟨ck, rs, he, hp, ?_⟩
       rw [hs]
       omega)

end SteppedFlapjack.StackAllocSteps
