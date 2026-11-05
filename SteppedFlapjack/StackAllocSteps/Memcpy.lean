import SteppedFlapjack.StackAllocSteps.GcNone

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The five-instruction memcpy loop body executes at most nine StackSem nodes. -/
theorem memcpyBodySteps (s : StackSemStateFiniteExact width C F) :
    steps (listSeqHOL [loadInst 1 2, addBytesInWordInst 2, sub1Inst 0,
      storeInst 1 3, addBytesInWordInst 3], s) ≤ 9 := by
  simp only [listSeqHOL, loadInst, storeInst, addBytesInWordInst, sub1Inst]
  refine stepsSeqLe _ _ 1 7 ?_ ?_ s
  · intro t; exact (steps_leaf _ t rfl).le
  · intro t; refine stepsSeqLe _ _ 1 5 ?_ ?_ t
    · intro t; exact (steps_leaf _ t rfl).le
    · intro t; refine stepsSeqLe _ _ 1 3 ?_ ?_ t
      · intro t; exact (steps_leaf _ t rfl).le
      · intro t; refine stepsSeqLe _ _ 1 1 ?_ ?_ t
        · intro t; exact (steps_leaf _ t rfl).le
        · intro t; exact (steps_leaf _ t rfl).le

/-- A loop with a uniformly bounded body is bounded by its available clock. -/
theorem loopStepsLe (body : HolProg width) (B : Nat)
    (hb : ∀ s : StackSemStateFiniteExact width C F, steps (body, s) ≤ B)
    (s : StackSemStateFiniteExact width C F) :
    steps (.loop body, s) ≤ (B + 1) * (s.clock + 1) := by
  induction hm : s.clock using Nat.strong_induction_on generalizing s with
  | h n ih =>
    rw [steps_loop]
    have hbody := hb s
    have hclock := Flapjack.StackSemMeasure.fixClock_clock_le s (Flapjack.StackSemEvaluate.evaluate (body, s))
    cases hfix : Flapjack.StackSemControl.fixClock s (Flapjack.StackSemEvaluate.evaluate (body, s)) with
    | mk r t =>
      simp only [hfix] at hclock ⊢
      split
      · rename_i hcont
        have hne : t.clock ≠ 0 := hcont.2
        have hlt : (Flapjack.StackSemStateOps.decClock t).clock < n := by
          simp only [Flapjack.StackSemStateOps.decClock]; omega
        have hi := ih _ hlt (Flapjack.StackSemStateOps.decClock t) rfl
        have hmul := Nat.mul_le_mul_left (B + 1) (show (Flapjack.StackSemStateOps.decClock t).clock + 1 ≤ n by omega)
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · rw [Nat.mul_add, Nat.mul_one]
        omega

/-- Memory-copy code is bounded by twelve nodes per available clock tick. -/
theorem memcpyStepsLe (s : StackSemStateFiniteExact width C F) :
    steps (Flapjack.Compiler.Backend.StackAlloc.memcpyCode, s) ≤ 12 * (s.clock + 1) := by
  change steps (.loop (.ite .notEqual 0 (.imm 0)
    (listSeqHOL [loadInst 1 2, addBytesInWordInst 2, sub1Inst 0,
      storeInst 1 3, addBytesInWordInst 3]) (.break 0)), s) ≤ _
  refine loopStepsLe _ 11 ?_ s
  intro t
  refine stepsIteLe _ _ _ _ _ 9 1 ?_ ?_ t
  · exact memcpyBodySteps
  · intro u; exact (steps_leaf _ u rfl).le

end SteppedFlapjack.StackAllocSteps
