import SteppedFlapjack.CrepToLoopSteps.Branch

/-! Source clock consumption is bounded by statement visits. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack
open SteppedFlapjack.CrepToLoopSteps

/-- Clock consumed by a supported Crep expression program is bounded by its
actual evaluator visits. -/
theorem exprProgram_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ExprProgram p)
    (source final : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (run : evalCrepSemHOLProgExact source p = (result,final)) :
    source.clock - final.clock ≤ steps p source := by
  induction shape generalizing source final result with
  | @leaf q leaf =>
    have one : steps q source = 1 := by apply steps_leaf; cases leaf <;> rfl
    rw [one]
    cases leaf with
    | skip => rw [evalCrepSemHOLProgExact_skip] at run; cases run; omega
    | «break» n => rw [evalCrepSemHOLProgExact_break] at run; cases run; omega
    | «continue» n => rw [evalCrepSemHOLProgExact_continue] at run; cases run; omega
    | tick =>
      rw [evalCrepSemHOLProgExact_tick] at run
      split at run <;> cases run <;> simp [decClockCrepSemHOL,CrepSemHOLState.emptyLocals]; omega
  | returnNil =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_return_holShape] at *
    split at run <;> cases run <;> simp [CrepSemHOLState.emptyLocals]
  | returnOne expr =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_return_holShape] at *
    split at run <;> cases run <;> simp [CrepSemHOLState.emptyLocals]
  | assign name expr =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_assign_holShape] at *
    repeat' first | split at run | cases run
    all_goals simp
  | storeGlob name expr =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_storeGlob_holShape] at *
    split at run <;> cases run <;> simp [CrepSemHOLState.setGlobals]
  | store dst src =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_store_holShape] at *
    repeat' first | split at run | cases run
    all_goals simp
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    rw [evalCrepSemHOLProgExact_seq_holShape] at run
    rcases firstRun : evalCrepSemHOLProgExact source a with ⟨firstResult,middle⟩
    rw [firstRun] at run
    have firstBound := iha source middle firstResult firstRun
    have firstClock := evalCrepSemHOLProgExact_clock_le source a
    rw [firstRun] at firstClock
    cases firstResult with
    | none =>
      simp only [if_true] at run
      simp only
      have secondBound := ihb middle final result run
      have secondClock := evalCrepSemHOLProgExact_clock_le middle b
      rw [run] at secondClock
      simp only at firstClock secondClock
      omega
    | some r =>
      simp only [if_false,Option.some_ne_none,Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega

/-- Clock consumption is bounded by visits for branch programs, including
sequences whose selected branch exits early. -/
theorem branchProgram_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : BranchProgram p)
    (source final : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (run : evalCrepSemHOLProgExact source p = (result,final)) :
    source.clock - final.clock ≤ steps p source := by
  induction shape generalizing source final result with
  | expr shape => exact exprProgram_clock_consumed shape source final result run
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    rw [evalCrepSemHOLProgExact_seq_holShape] at run
    rcases firstRun : evalCrepSemHOLProgExact source a with ⟨firstResult,middle⟩
    rw [firstRun] at run
    have firstBound := iha source middle firstResult firstRun
    have firstClock := evalCrepSemHOLProgExact_clock_le source a
    rw [firstRun] at firstClock
    cases firstResult with
    | none =>
      simp only [if_true] at run
      simp only
      have secondBound := ihb middle final result run
      have secondClock := evalCrepSemHOLProgExact_clock_le middle b
      rw [run] at secondClock
      simp only at firstClock secondClock
      omega
    | some r =>
      simp only [if_false,Option.some_ne_none,Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega
  | @ite cond a b hcond ha hb iha ihb =>
    rw [steps_ite,evalCrepSemHOLProgExact_ite_holShape] at *
    rcases hv : evalCrepSemHOLExp source cond with _ | ⟨v⟩
    · simp only [hv,Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega
    · simp only [hv] at run ⊢
      by_cases nz : v.1 ≠ 0
      · simp only [if_pos nz] at run ⊢
        have h := iha source final result run
        omega
      · simp only [if_neg nz] at run ⊢
        have h := ihb source final result run
        omega

end SteppedFlapjack.CrepSteps
