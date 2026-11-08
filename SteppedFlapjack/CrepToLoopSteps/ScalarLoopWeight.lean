import SteppedFlapjack.CrepToLoopSteps.ScalarLoopLive
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]
/-- Counts executable control nodes, ignoring administrative marks and data. -/
def loopSkeletonWeight : HolLoopProg width → Nat
  | .mark p => loopSkeletonWeight p
  | .seq a b => 1 + loopSkeletonWeight a + loopSkeletonWeight b
  | .ite _ _ _ a b _ => 1 + loopSkeletonWeight a + loopSkeletonWeight b
  | .loop _ body _ => 1 + loopSkeletonWeight body
  | _ => 1

private theorem branch_shrink_weight {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ lt live, loopSkeletonWeight (shrinkHOL lt p live).1 = loopSkeletonWeight p := by
  induction shape with
  | skip | tick | store | setGlobal | ret | «break» | «continue» => intros; simp only [shrinkHOL,loopSkeletonWeight]
  | assign v e => intro lt live; simp only [shrinkHOL]; cases sptLookup v live <;> rfl
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL,loopSkeletonWeight,iha,ihb]
  | mark h ih => intro lt live; simpa only [shrinkHOL,loopSkeletonWeight] using ih lt live
  | ite cmp r ri ls ha hb iha ihb =>
    intro lt live
    cases ri <;> simp only [shrinkHOL,loopSkeletonWeight,iha,ihb]

theorem scalarLoop_shrink_weight {p : HolLoopProg width} (shape : ScalarLoop p) :
    ∀ lt live, loopSkeletonWeight (shrinkHOL lt p live).1 = loopSkeletonWeight p := by
  induction shape with
  | branch h => exact branch_shrink_weight h
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL,loopSkeletonWeight,iha,ihb]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    intro lt live
    cases ri <;> simp only [shrinkHOL,loopSkeletonWeight,iha,ihb]
  | @loop li lo body hb ih =>
    intro lt live
    simp only [shrinkHOL]
    generalize heq : fixedpointHOL lt li .ln (sptUnion li (sptInter lo live)) body = outcome
    cases outcome with
    | none => simp only [loopSkeletonWeight,ih]
    | some pair =>
      rcases pair with ⟨b,l⟩
      simp only [loopSkeletonWeight, scalarFixedpoint_preserves (fun p => loopSkeletonWeight p = loopSkeletonWeight body) ih lt li .ln _ b l heq]
private theorem branch_mark_weight {p : HolLoopProg width} (shape : LoopBranch p) :
    loopSkeletonWeight (markAllHOL p).1 = loopSkeletonWeight p := by
  induction shape with
  | skip | tick | assign | store | setGlobal | ret | «break» | «continue» => rfl
  | mark h ih => simpa only [markAllHOL,loopSkeletonWeight] using ih
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h : (markAllHOL a).2 <;> cases k : (markAllHOL b).2 <;>
      simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_true,if_false,loopSkeletonWeight,iha,ihb]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h : (markAllHOL a).2 <;> cases k : (markAllHOL b).2 <;>
      simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_true,if_false,loopSkeletonWeight,iha,ihb]

theorem scalarLoop_mark_weight {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopSkeletonWeight (markAllHOL p).1 = loopSkeletonWeight p := by
  induction shape with
  | branch h => exact branch_mark_weight h
  | @loop li lo body h ih => simp only [markAllHOL,loopSkeletonWeight,ih]
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h : (markAllHOL a).2 <;> cases k : (markAllHOL b).2 <;>
      simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_true,if_false,loopSkeletonWeight,iha,ihb]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h : (markAllHOL a).2 <;> cases k : (markAllHOL b).2 <;>
      simp only [Bool.false_and,Bool.true_and,Bool.false_eq_true,if_true,if_false,loopSkeletonWeight,iha,ihb]

theorem scalarLoop_optimise_weight {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopSkeletonWeight (optimiseHOL p) = loopSkeletonWeight p := by
  rw [optimiseHOL,scalarLoop_call shape .ln,compHOL]
  rw [scalarLoop_mark_weight (scalarLoop_shrink shape [] .ln), scalarLoop_shrink_weight shape [] .ln]

private theorem branch_weight_le_size {p : HolLoopProg width} (shape : LoopBranch p) :
    loopSkeletonWeight p ≤ sizeOf p := by
  induction shape <;> simp_all [loopSkeletonWeight] <;> omega

theorem scalarLoop_weight_le_size {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopSkeletonWeight p ≤ sizeOf p := by
  induction shape with
  | branch h => exact branch_weight_le_size h
  | seq _ _ a b => simp only [loopSkeletonWeight]; simp_wf; omega
  | ite _ _ _ _ _ _ a b => simp only [loopSkeletonWeight]; simp_wf; omega
  | loop _ _ _ ih => simp only [loopSkeletonWeight]; simp_wf; omega

/-- The complete optimized output bounds the original control-node count. -/
theorem scalarLoop_weight_le_optimised_size {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopSkeletonWeight p ≤ sizeOf (optimiseHOL p) := by
  rw [← scalarLoop_optimise_weight shape]
  exact scalarLoop_weight_le_size (scalarLoop_optimise shape)

end SteppedFlapjack.CrepToLoopSteps
