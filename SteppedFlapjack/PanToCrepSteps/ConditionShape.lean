import SteppedFlapjack.PanToCrepSteps.Shape
import SteppedFlapjack.CrepToLoopSteps.ConditionShape

/-! Pancake comparison conditions through the actual frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.CrepToLoopSteps

/-- Scalar conditions and comparisons of supported scalar expressions. -/
inductive BranchCondition {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) : ExpHOL width → Prop
  | scalar {e} : ScalarExpression context e → BranchCondition context e
  | cmp (op) {a b} : ScalarExpression context a → ScalarExpression context b →
      BranchCondition context (.cmp op a b)

/-- A supported Pancake condition lowers to one supported Crep condition. -/
theorem branchCondition_compile {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {e : ExpHOL width} (shape : BranchCondition context e) :
    ∃ value, compileExpExactHOLW context e = ([value],.one) ∧ CrepToLoopSteps.BranchCondition value := by
  cases shape with
  | scalar h =>
    obtain ⟨value,compiled,direct⟩ := scalar_compile h
    exact ⟨value,compiled,.direct direct⟩
  | @cmp op a b ha hb =>
    obtain ⟨va,ca,da⟩ := scalar_compile ha
    obtain ⟨vb,cb,db⟩ := scalar_compile hb
    exact ⟨.cmp op va vb,by simp [compileExpExactHOLW,ca,cb],.cmp op da db⟩

/-- The actual frontend emits the comparison condition and branch body used by
the generalized Crep loop compiler. -/
theorem branchConditionWhile_compile {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {condition : ExpHOL width} {body : ProgHOL width}
    (hc : BranchCondition context condition) (hb : BranchProgram context body) :
    ∃ conditionCrep,
      compileProgExactHOLW context (.while condition body) =
        .while conditionCrep (compileProgExactHOLW context body) ∧
      CrepToLoopSteps.BranchCondition conditionCrep ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW context body) := by
  obtain ⟨value,compiled,shape⟩ := branchCondition_compile hc
  exact ⟨value,by simp [compileProgExactHOLW,compileWhileExactHOLW,compiled],shape,branch_compile hb⟩

end SteppedFlapjack.PanToCrepSteps
