import Flapjack.Pancake.PanToCrep.CompileExact
import SteppedFlapjack.CrepToLoopSteps.WhileRiscV

/-! Pancake syntax which the actual frontend lowers into the proven Crep fragment. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang
open SteppedFlapjack.CrepToLoopSteps

/-- Scalar expressions with exact singleton local-variable representations. -/
inductive ScalarExpression {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) : ExpHOL width → Prop
  | const (v) : ScalarExpression context (.const v)
  | local (name n) : context.vars.lookup name = some (.one,[n]) → ScalarExpression context (.var .local name)
  | baseAddr : ScalarExpression context .baseAddr
  | topAddr : ScalarExpression context .topAddr
  | bytesInWord : ScalarExpression context .bytesInWord
  | shift (op) {a b} : ScalarExpression context a → ScalarExpression context b → ScalarExpression context (.shift op a b)
  | op (operator) {a b} : ScalarExpression context a → ScalarExpression context b → ScalarExpression context (.op operator [a,b])

/-- These expressions lower to one direct Crep expression. -/
theorem scalar_compile {width : Nat} [NeZero width] {context : PanToCrepContextExact width}
    {e : ExpHOL width} (shape : ScalarExpression context e) :
    ∃ value, compileExpExactHOLW context e = ([value],.one) ∧ DirectExpression value := by
  induction shape with
  | const v => exact ⟨_,by simp [compileExpExactHOLW],.const v⟩
  | «local» name n found => exact ⟨_,by simp [compileExpExactHOLW,found],.var n⟩
  | baseAddr => exact ⟨_,by simp [compileExpExactHOLW],.baseAddr⟩
  | topAddr => exact ⟨_,by simp [compileExpExactHOLW],.topAddr⟩
  | bytesInWord => exact ⟨.const (BitVec.ofNat width (width / 8)),by simp [compileExpExactHOLW],.const _⟩
  | shift op ha hb iha ihb =>
    obtain ⟨a,ca,da⟩ := iha
    obtain ⟨b,cb,db⟩ := ihb
    exact ⟨_,by simp only [compileExpExactHOLW,ca,cb],.shift op da db⟩
  | op operator ha hb iha ihb =>
    obtain ⟨a,ca,da⟩ := iha
    obtain ⟨b,cb,db⟩ := ihb
    exact ⟨_,by simp [compileExpExactHOLW,compileExpExactHOLWList,ca,cb,cexpHeads],.op operator da db⟩

/-- A loop-free source fragment with scalar expressions and direct assignments. -/
inductive BranchProgram {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) : ProgHOL width → Prop
  | skip : BranchProgram context .skip
  | break : BranchProgram context .break
  | continue : BranchProgram context .continue
  | tick : BranchProgram context .tick
  | return {e} : ScalarExpression context e → BranchProgram context (.return e)
  | assign (name n) {e} : context.vars.lookup name = some (.one,[n]) →
      ScalarExpression context e →
      (∀ value, compileExpExactHOLW context e = ([value],.one) →
        distinctListsHol [n] (crepExpVarsW (crepExpOfHOL value)) = true) →
      BranchProgram context (.assign .local name e)
  | seq {a b} : BranchProgram context a → BranchProgram context b → BranchProgram context (.seq a b)
  | ite {e a b} : ScalarExpression context e → BranchProgram context a → BranchProgram context b →
      BranchProgram context (.ite e a b)

/-- Actual `compile_def` output is accepted by the existing Crep branch proof. -/
theorem branch_compile {width : Nat} [NeZero width] {context : PanToCrepContextExact width}
    {p : ProgHOL width} (shape : BranchProgram context p) :
    CrepToLoopSteps.BranchProgram (compileProgExactHOLW context p) := by
  induction shape with
  | skip => simpa [compileProgExactHOLW] using (CrepToLoopSteps.BranchProgram.expr (.leaf .skip))
  | «break» => simpa [compileProgExactHOLW] using (CrepToLoopSteps.BranchProgram.expr (.leaf (.break 0)))
  | «continue» => simpa [compileProgExactHOLW] using (CrepToLoopSteps.BranchProgram.expr (.leaf (.continue 0)))
  | tick => simpa [compileProgExactHOLW] using (CrepToLoopSteps.BranchProgram.expr (.leaf .tick))
  | «return» he =>
    obtain ⟨value,compiled,direct⟩ := scalar_compile he
    simpa [compileProgExactHOLW,compileReturnExactHOLW,compiled,sizeOfShapeHOL] using
      (CrepToLoopSteps.BranchProgram.expr (ExprProgram.returnOne direct))
  | @assign name n e found he disjoint =>
    obtain ⟨value,compiled,direct⟩ := scalar_compile he
    have hd := disjoint value compiled
    simp [compileProgExactHOLW,compileLocalAssignExactHOLW,compiled,found,hd,crepNestedSeqHOL]
    exact .seq (.expr (.assign n direct)) (.expr (.leaf .skip))
  | seq ha hb iha ihb => simpa only [compileProgExactHOLW] using CrepToLoopSteps.BranchProgram.seq iha ihb
  | ite he ha hb iha ihb =>
    obtain ⟨value,compiled,direct⟩ := scalar_compile he
    simpa [compileProgExactHOLW,compileIfExactHOLW,compiled] using CrepToLoopSteps.BranchProgram.ite direct iha ihb

/-- A scalar-condition Pancake while lowers to a direct-condition Crep loop
with a body in the established branch fragment. -/
theorem while_compile {width : Nat} [NeZero width] {context : PanToCrepContextExact width}
    {condition : ExpHOL width} {body : ProgHOL width}
    (hc : ScalarExpression context condition) (hb : BranchProgram context body) :
    ∃ conditionCrep,
      compileProgExactHOLW context (.while condition body) =
        .while conditionCrep (compileProgExactHOLW context body) ∧
      DirectExpression conditionCrep ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW context body) := by
  obtain ⟨value,compiled,direct⟩ := scalar_compile hc
  exact ⟨value,by simp [compileProgExactHOLW,compileWhileExactHOLW,compiled],direct,branch_compile hb⟩

end SteppedFlapjack.PanToCrepSteps
