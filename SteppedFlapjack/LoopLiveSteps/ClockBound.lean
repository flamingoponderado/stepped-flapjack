import SteppedFlapjack.LoopLiveSteps.OptimiseShape
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopConsumption
import Flapjack.Pancake.Proofs.LoopLive.Optimise

/-! Source-clock visit bound for the actual Loop optimizer output. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- Recursive Loop source shapes are exactly within the established scalar fragment. -/
theorem sequence_scalarLoop {p : HolLoopProg width} (shape : LoopSequenceSource p) :
    SteppedFlapjack.CrepToLoopSteps.ScalarLoop p := by
  induction shape with
  | branch h => exact .branch h
  | loop live exits h => exact .loop live exits (.branch h)
  | seq ha hb iha ihb => exact .seq iha ihb
  | nestedLoop live exits h ih => exact .loop live exits ih
  | conditional cmp r ri live ha hb iha ihb => exact .ite cmp r ri live iha ihb

/-- Source visits, including nested loops, are bounded by code size and clock. -/
theorem sequence_clock_bound {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s : LoopSemStateFiniteExact width F) : steps p s ≤ sizeOf p * (s.clock+1) := by
  rcases run : evaluate p s with ⟨result,post⟩
  have bound := SteppedFlapjack.CrepToLoopSteps.scalarLoop_consumption_bound (sequence_scalarLoop shape) s post result run
  have clocks : s.clock - post.clock + 1 ≤ s.clock + 1 := by omega
  exact bound.trans (Nat.mul_le_mul_left _ clocks)

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
