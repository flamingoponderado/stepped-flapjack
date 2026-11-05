import SteppedFlapjack.StackAllocSteps.ControlSteps
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect Flapjack.Compiler.Backend.StackProps
open Flapjack.StackSemEvaluate SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width]

/-- The structural loop cost grows monotonically with its clock budget. -/
theorem loopOnlyCostMono (p : HolProg width) {a b : Nat} (h : a ≤ b) :
    loopOnlyCost a p ≤ loopOnlyCost b p := by
  cases hp : p <;> simp only [loopOnlyCost]
  case seq p q =>
    exact Nat.add_le_add (Nat.add_le_add_left (loopOnlyCostMono p h) 1) (loopOnlyCostMono q h)
  case ite cmp r ri p q =>
    exact Nat.add_le_add (Nat.add_le_add_left (loopOnlyCostMono p h) 1) (loopOnlyCostMono q h)
  case loop p =>
    exact Nat.mul_le_mul (Nat.add_le_add_right (loopOnlyCostMono p h) 1) (Nat.add_le_add_right h 1)
  all_goals exact Nat.le_refl _
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- The collector allocation cost increases with stack length. -/
theorem allocGcStepCostMono (c : Config) {a b : Nat} (h : a ≤ b) :
    allocGcStepCost (width := width) c a ≤ allocGcStepCost (width := width) c b := by
  unfold allocGcStepCost
  split
  · exact Nat.le_refl _
  · unfold simpleAllocClockBudget simpleGcStepCost
    dsimp only
    gcongr
  · apply max_le_max <;> apply loopOnlyCostMono <;> gcongr

/-- For a word of at least one byte, the semantic stack bound gives a uniform
stack-length bound depending only on the word width. -/
theorem stackLengthBound {C F : Type} (s : StackSemStateFiniteExact width C F)
    (hwidth : 8 ≤ width) (hstack : s.stack.length * (width / 8) < 2 ^ width) :
    s.stack.length ≤ 2 ^ width := by
  have h : 1 ≤ width / 8 := Nat.div_pos hwidth (by decide)
  have hm : s.stack.length ≤ s.stack.length * (width / 8) := by
    simpa using Nat.mul_le_mul_left s.stack.length h
  omega

/-- One factor, independent of runtime stack length, suffices for every leaf. -/
theorem boundedLeafUniform {C F : Type} (anything : WordSemGcFun width)
    (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hleaf : isRecursive p = false) :
    ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
      (m n : Nat) (regs : HolFiniteMapExact Nat (WordLocW width)),
      evaluate (p, s) = (r, t) → r ≠ some .error → allocArg p → Pre cr c s regs →
      ∃ ck regs1, evaluate ((comp n m p).1, Tgt anything cr c s ck regs) =
          (r, Res anything cr c t regs1) ∧ Post r t regs1 ∧
        steps ((comp n m p).1, Tgt anything cr c s ck regs) ≤
          max 5 (4 + allocGcStepCost (width := width) c (2 ^ width)) * steps (p, s) := by
  intro r t m n regs h hr ha hpre
  obtain ⟨ck, regs1, he, hp, hs⟩ := leafSteps anything cr p s hleaf r t m n c regs h hr ha hpre
  have hm := allocGcStepCostMono (width := width) c (stackLengthBound s hwidth hpre.stack)
  refine ⟨ck, regs1, he, hp, ?_⟩
  rw [steps_leaf p s hleaf, Nat.mul_one]
  exact hs.trans (max_le_max (Nat.le_refl _) (Nat.add_le_add_left hm 4))

end SteppedFlapjack.StackAllocSteps
