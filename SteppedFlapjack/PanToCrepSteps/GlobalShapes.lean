import SteppedFlapjack.PanToCrepSteps.ControlSteps
import Flapjack.Pancake.PanGlobals.CompileExpExact

/-! The globals pass preserves the supported source syntax. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- Global lowering keeps every supported scalar expression in the scalar
fragment, including its explicit adjustment of `topAddr`. -/
theorem globalCompile_scalar_shape {width : Nat} [NeZero width]
    (globals : PanGlobalsContextExact width) {ctxt : PanToCrepContextExact width}
    {expr : ExpHOL width} (shape : ScalarExpression ctxt expr) :
    ScalarExpression ctxt (compileExpExactHOL globals expr) := by
  induction shape with
  | const v => simpa only [compileExpExactHOL] using (ScalarExpression.const (context := ctxt) v)
  | «local» name n found => simpa only [compileExpExactHOL] using (ScalarExpression.local name n found)
  | baseAddr => simpa only [compileExpExactHOL] using (ScalarExpression.baseAddr (context := ctxt))
  | topAddr => simpa only [compileExpExactHOL] using (ScalarExpression.op .sub (ScalarExpression.topAddr (context := ctxt)) (.const globals.maxGlobalsSize))
  | bytesInWord => simpa only [compileExpExactHOL] using (ScalarExpression.bytesInWord (context := ctxt))
  | shift op ha hb iha ihb => simpa only [compileExpExactHOL] using (ScalarExpression.shift op iha ihb)
  | op operator ha hb iha ihb =>
    simpa only [compileExpExactHOL,compileExpExactHOLList] using (ScalarExpression.op operator iha ihb)

/-- Global lowering preserves the supported loop-free branch fragment. -/
theorem globalCompile_branch_shape {width : Nat} [NeZero width]
    (globals : PanGlobalsContextExact width) {ctxt : PanToCrepContextExact width}
    {prog : ProgHOL width} (shape : BranchProgram ctxt prog) :
    BranchProgram ctxt (compileProgExactHOL globals prog) := by
  induction shape with
  | skip => simpa only [compileProgExactHOL] using (BranchProgram.skip (context := ctxt))
  | «break» => simpa only [compileProgExactHOL] using (BranchProgram.break (context := ctxt))
  | «continue» => simpa only [compileProgExactHOL] using (BranchProgram.continue (context := ctxt))
  | tick => simpa only [compileProgExactHOL] using (BranchProgram.tick (context := ctxt))
  | «return» he => simpa only [compileProgExactHOL] using (BranchProgram.return (globalCompile_scalar_shape globals he))
  | assign name n found he => simpa only [compileProgExactHOL] using (BranchProgram.assign name n found (globalCompile_scalar_shape globals he))
  | seq ha hb iha ihb => simpa only [compileProgExactHOL] using (BranchProgram.seq iha ihb)
  | ite he ha hb iha ihb => simpa only [compileProgExactHOL] using (BranchProgram.ite (globalCompile_scalar_shape globals he) iha ihb)

/-- A supported loop-free Pancake branch visits at most its syntax size,
independently of the initial state. -/
theorem branch_control_static {width : Nat} [NeZero width] {F : Type}
    {ctxt : PanToCrepContextExact width} {prog : ProgHOL width}
    (shape : BranchProgram ctxt prog) (state : PanSemStateFiniteExact width F) :
    controlSteps prog state ≤ sizeOf prog := by
  induction shape generalizing state with
  | skip => rw [controlSteps.eq_def]; simp_wf
  | «break» => rw [controlSteps.eq_def]; simp_wf
  | «continue» => rw [controlSteps.eq_def]; simp_wf
  | tick => rw [controlSteps.eq_def]; simp_wf
  | «return» he => rw [controlSteps.eq_def]; simp_wf
  | assign name n found he => rw [controlSteps.eq_def]; simp_wf; omega
  | @seq a b ha hb iha ihb =>
    rw [controlSteps_seq]
    have first := iha state
    rcases state.evaluateHOLFiniteState a with ⟨result,post⟩
    cases result with
    | none => have second := ihb post; simp_wf; omega
    | some result => simp_wf; omega
  | @ite e a b he ha hb iha ihb =>
    rw [controlSteps.eq_def]
    have left : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
        (state.clock,sizeOf a) (state.clock,sizeOf (.ite e a b : ProgHOL width)) := by
      apply Prod.Lex.right
      simp_wf
      omega
    have right : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
        (state.clock,sizeOf b) (state.clock,sizeOf (.ite e a b : ProgHOL width)) := by
      apply Prod.Lex.right
      simp_wf
    simp only [dif_pos left,dif_pos right]
    have first := iha state
    have second := ihb state
    classical
    rcases heval : @evalHOLExact width F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) e with _ | value
    · simp_wf; omega
    · cases value with
      | val value =>
        cases value with
        | word w => simp_wf; split <;> omega
      | rStruct fields => simp_wf; omega
      | nStruct name fields => simp_wf; omega

/-- Global lowering of a loop-free branch has a source-visit bound with an
explicit compiled-syntax factor, without assuming related states. -/
theorem globalCompile_branch_steps {width : Nat} [NeZero width] {F G : Type}
    (globals : PanGlobalsContextExact width) {ctxt : PanToCrepContextExact width}
    {prog : ProgHOL width} (shape : BranchProgram ctxt prog)
    (source : PanSemStateFiniteExact width F) (target : PanSemStateFiniteExact width G) :
    controlSteps (compileProgExactHOL globals prog) target ≤
      sizeOf (compileProgExactHOL globals prog) * controlSteps prog source := by
  have bounded := branch_control_static (globalCompile_branch_shape globals shape) target
  have positive := controlSteps_pos prog source
  nlinarith

/-- The globals pass preserves the initialized-loop-tail decomposition and
supplies each lowered component with the shapes used by the machine theorem. -/
theorem globalCompile_loop_shapes {width : Nat} [NeZero width]
    (globals : PanGlobalsContextExact width) (ctxt : PanToCrepContextExact width)
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (initShape : BranchProgram ctxt init) (conditionShape : ScalarExpression ctxt condition)
    (bodyShape : BranchProgram ctxt body) (tailShape : BranchProgram ctxt tail) :
    BranchProgram ctxt (compileProgExactHOL globals init) ∧
    ScalarExpression ctxt (compileExpExactHOL globals condition) ∧
    BranchProgram ctxt (compileProgExactHOL globals body) ∧
    BranchProgram ctxt (compileProgExactHOL globals tail) ∧
    compileProgExactHOL globals (.seq init (.seq (.while condition body) tail)) =
      .seq (compileProgExactHOL globals init)
        (.seq (.while (compileExpExactHOL globals condition) (compileProgExactHOL globals body))
          (compileProgExactHOL globals tail)) := by
  exact ⟨globalCompile_branch_shape globals initShape,globalCompile_scalar_shape globals conditionShape,
    globalCompile_branch_shape globals bodyShape,globalCompile_branch_shape globals tailShape,by simp only [compileProgExactHOL]⟩

end SteppedFlapjack.PanToCrepSteps
