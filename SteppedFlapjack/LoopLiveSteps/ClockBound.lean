import SteppedFlapjack.LoopLiveSteps.OptimiseShape
import SteppedFlapjack.LoopSteps.IterationClock
import Flapjack.Pancake.Proofs.LoopLive.Optimise

/-! Source-clock visit bound for the actual Loop optimizer output. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

theorem branch_branched {p : HolLoopProg width} (shape : LoopBranch p) : BranchedProgram p := by
  induction shape with
  | skip => exact .leaf .skip
  | tick => exact .leaf .tick
  | assign v e => exact .leaf (.assign v e)
  | store e v => exact .leaf (.store e v)
  | setGlobal v e => exact .leaf (.setGlobal v e)
  | ret vs => exact .leaf (.ret vs)
  | «break» n => exact .leaf (.break n)
  | «continue» n => exact .leaf (.continue n)
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | mark _ ih => exact .mark ih
  | ite cmp r ri live _ _ ih1 ih2 => exact .ite cmp r ri live ih1 ih2

/-- Source visits in a sequence of branch-bodied loops are bounded by program
syntax and the available Loop clock, including error and timeout outcomes. -/
theorem sequence_clock_bound {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s : LoopSemStateFiniteExact width F) : steps p s ≤ sizeOf p * (s.clock+1) := by
  induction shape generalizing s with
  | branch h =>
    have bound := branchedProgram_static_bound (branch_branched h) s
    nlinarith
  | @loop live exits body h =>
    rcases run : evaluate (.loop live body exits) s with ⟨res,post⟩
    have bound := loop_steps_by_clock_consumption live exits body (branch_branched h) s post res run
    have size : 1 + sizeOf body ≤ sizeOf (.loop live body exits : HolLoopProg width) := by simp_wf; omega
    have clocks : s.clock - post.clock + 1 ≤ s.clock+1 := by omega
    exact bound.trans ((Nat.mul_le_mul_left _ clocks).trans (Nat.mul_le_mul_right _ size))
  | @seq a b ha hb iha ihb =>
    have size : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : HolLoopProg width) := by simp_wf
    rw [steps_seq]
    have first := iha s
    rcases run : evaluate a s with ⟨res,post⟩
    cases res with
    | some r => simp only; nlinarith
    | none =>
      have second := ihb post
      have clock := evaluate_clock a s none post run
      simp only
      nlinarith

/-- The actual Loop optimizer preserves supported shape and yields a visit
bound computed from optimized syntax and source clock. -/
theorem optimise_clock_bound {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s : LoopSemStateFiniteExact width F) :
    steps (optimiseHOL p) s ≤ sizeOf (optimiseHOL p) * (s.clock+1) :=
  sequence_clock_bound (optimise_sequence shape) s

/-- A completed run is preserved by the actual optimizer with a proved
optimized-program visit bound. -/
theorem optimise_complete_with_steps {p : HolLoopProg 64} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    LoopSequenceSource (optimiseHOL p) ∧
    steps (optimiseHOL p) s ≤ sizeOf (optimiseHOL p) * (s.clock+1) := by
  refine ⟨optimise_correct p s result post ⟨run,?_,?_,?_,?_⟩,optimise_sequence shape,optimise_clock_bound shape s⟩
  all_goals cases complete <;> simp_all

end SteppedFlapjack.LoopLiveSteps
