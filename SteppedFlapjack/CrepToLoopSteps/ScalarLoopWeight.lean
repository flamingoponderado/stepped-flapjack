import SteppedFlapjack.CrepToLoopSteps.ScalarLoopLive
import SteppedFlapjack.LoopSteps.BranchedStatic
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

/-- Control-node count including marks, used to bound evaluator visits. -/
def loopVisitWeight : HolLoopProg width → Nat
  | .mark p => 1 + loopVisitWeight p
  | .seq a b => 1 + loopVisitWeight a + loopVisitWeight b
  | .ite _ _ _ a b _ => 1 + loopVisitWeight a + loopVisitWeight b
  | .loop _ body _ => 1 + loopVisitWeight body
  | _ => 1

theorem loopVisitWeight_pos (p : HolLoopProg width) : 0 < loopVisitWeight p := by
  cases p <;> simp [loopVisitWeight]

/-- Appending statements to a nested sequence cannot reduce its control weight. -/
theorem nestedSeq_append_weight (a b : List (HolLoopProg width)) :
    loopVisitWeight (loopNestedSeqHOL a) ≤ loopVisitWeight (loopNestedSeqHOL (a ++ b)) := by
  induction a with
  | nil => simp only [List.nil_append,loopNestedSeqHOL,loopVisitWeight]; exact loopVisitWeight_pos _
  | cons p rest ih => simp only [List.cons_append,loopNestedSeqHOL,loopVisitWeight]; omega

theorem branched_visitWeight {p : HolLoopProg width}
    (shape : SteppedFlapjack.LoopToWordSteps.BranchedProgram p) :
    loopVisitWeight p = LoopSteps.structuralWeight p := by
  induction shape with
  | leaf h => cases h <;> rfl
  | mark _ ih => simp only [loopVisitWeight,LoopSteps.structuralWeight,ih]
  | seq _ _ a b => simp only [loopVisitWeight,LoopSteps.structuralWeight,a,b]
  | ite _ _ _ _ _ _ a b => simp only [loopVisitWeight,LoopSteps.structuralWeight,a,b]

theorem branch_visitWeight {p : HolLoopProg width} (shape : LoopBranch p) :
    loopVisitWeight p = LoopSteps.structuralWeight p := by
  induction shape <;> simp_all [loopVisitWeight,LoopSteps.structuralWeight]

theorem scalarLoop_visitWeight_le_size {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopVisitWeight p ≤ sizeOf p := by
  induction shape with
  | branch h =>
    induction h <;> simp_all [loopVisitWeight] <;> omega
  | seq _ _ a b => simp only [loopVisitWeight]; simp_wf; omega
  | ite _ _ _ _ _ _ a b => simp only [loopVisitWeight]; simp_wf; omega
  | loop _ _ _ ih => simp only [loopVisitWeight]; simp_wf; omega

/-- Ignoring marks cannot increase the control-node count. -/
theorem scalarLoop_skeleton_le_visitWeight {p : HolLoopProg width} (shape : ScalarLoop p) :
    loopSkeletonWeight p ≤ loopVisitWeight p := by
  induction shape with
  | branch h =>
    induction h <;> simp_all [loopSkeletonWeight,loopVisitWeight] <;> omega
  | seq _ _ a b => simp only [loopSkeletonWeight,loopVisitWeight]; omega
  | ite _ _ _ _ _ _ a b => simp only [loopSkeletonWeight,loopVisitWeight]; omega
  | loop _ _ _ ih => simp only [loopSkeletonWeight,loopVisitWeight]; omega

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

end SteppedFlapjack.CrepToLoopSteps
