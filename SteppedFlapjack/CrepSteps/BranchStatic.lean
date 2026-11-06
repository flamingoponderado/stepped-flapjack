import SteppedFlapjack.CrepSteps.BranchClock

/-! Static evaluator visit bounds for loop-free Crep branches. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack SteppedFlapjack.CrepToLoopSteps

/-- An expression-program execution visits no more nodes than its syntax size. -/
theorem exprProgram_static {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ExprProgram p) (source : CrepSemHOLState width σ) :
    steps p source ≤ sizeOf p := by
  induction shape generalizing source with
  | @leaf q leaf =>
    have h : steps q source = 1 := by apply steps_leaf; cases leaf <;> rfl
    rw [h]
    cases leaf <;> simp_wf
  | returnNil => rw [steps_leaf _ _ (by rfl)]; simp_wf
  | returnOne e => rw [steps_leaf _ _ (by rfl)]; simp_wf
  | assign name e => rw [steps_leaf _ _ (by rfl)]; simp_wf; omega
  | storeGlob name e => rw [steps_leaf _ _ (by rfl)]; simp_wf; omega
  | store a b => rw [steps_leaf _ _ (by rfl)]; simp_wf; omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    have first := iha source
    rcases evalCrepSemHOLProgExact source a with ⟨out,post⟩
    cases out with
    | none => have second := ihb post; simp_wf; omega
    | some r => simp_wf; omega

/-- A loop-free conditional Crep execution visits no more nodes than its syntax size. -/
theorem branchProgram_static {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : BranchProgram p) (source : CrepSemHOLState width σ) :
    steps p source ≤ sizeOf p := by
  induction shape generalizing source with
  | expr shape => exact exprProgram_static shape source
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    have first := iha source
    rcases evalCrepSemHOLProgExact source a with ⟨out,post⟩
    cases out with
    | none => have second := ihb post; simp_wf; omega
    | some r => simp_wf; omega
  | @ite e a b he ha hb iha ihb =>
    rw [steps_ite]
    have first := iha source
    have second := ihb source
    rcases evalCrepSemHOLExp source e with _ | ⟨v⟩
    · simp_wf; omega
    · cases v with
      | word w =>
        simp_wf
        split <;> omega

end SteppedFlapjack.CrepSteps
