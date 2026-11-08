import SteppedFlapjack.CrepSteps.BranchClock
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram

/-! Clock consumption for arbitrarily nested scalar Crep programs. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack
open SteppedFlapjack.CrepToLoopSteps

/-- Scalar Crep clock consumption is bounded by actual visits, including
nested loops and branches. -/
theorem scalarProgram_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ScalarProgram p)
    (source final : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (run : evalCrepSemHOLProgExact source p = (result,final)) :
    source.clock - final.clock ≤ steps p source := by
  induction shape generalizing source final result with
  | skip => exact exprProgram_clock_consumed (.leaf .skip) source final result run
  | «break» n => exact exprProgram_clock_consumed (.leaf (.break n)) source final result run
  | «continue» n => exact exprProgram_clock_consumed (.leaf (.continue n)) source final result run
  | tick => exact exprProgram_clock_consumed (.leaf .tick) source final result run
  | ret h =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_return_holShape] at *
    split at run <;> cases run <;> simp [CrepSemHOLState.emptyLocals]
  | assign name h =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_assign_holShape] at *
    repeat' first | split at run | cases run
    all_goals simp
  | store ha hb =>
    rw [steps_leaf _ _ (by rfl),evalCrepSemHOLProgExact_store_holShape] at *
    repeat' first | split at run | cases run
    all_goals simp
  | @dec name value body hv hb ih =>
    rw [steps_dec,evalCrepSemHOLProgExact_dec_holShape] at *
    rcases evalValue : evalCrepSemHOLExp source value with _ | v
    · simp only [evalValue,Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega
    · simp only [evalValue] at run ⊢
      rcases bodyRun : evalCrepSemHOLProgExact (CrepSemHOLState.setVar name v source) body with ⟨bodyResult,post⟩
      change evalCrepSemHOLProgExact {source with locals := source.locals.updateEq (name,v)} body = _ at bodyRun
      simp only [bodyRun,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have bound := ih (CrepSemHOLState.setVar name v source) post bodyResult (by simpa [CrepSemHOLState.setVar] using bodyRun)
      change source.clock - post.clock ≤ 1 + steps body (CrepSemHOLState.setVar name v source)
      change source.clock - post.clock ≤ steps body (CrepSemHOLState.setVar name v source) at bound
      omega
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

  | @«while» condition body hcondition hbody bodyIH =>
    induction hc : source.clock using Nat.strongRecOn generalizing source final result with
    | _ clock ih =>
      rw [evalCrepSemHOLProgExact_while_holShape] at run
      rw [steps_while]
      rcases hv : evalCrepSemHOLExp source condition with _ | ⟨w⟩
      · simp only [hv,Prod.mk.injEq] at run
        obtain ⟨_,rfl⟩ := run
        simp only
        omega
      · simp only [hv] at run ⊢
        by_cases nz : w.1 ≠ 0
        · simp only [if_pos nz] at run
          by_cases clockZero : source.clock = 0
          · simp only [clockZero,if_true,Prod.mk.injEq] at run
            obtain ⟨_,rfl⟩ := run
            simp [clockZero,CrepSemHOLState.emptyLocals]
            omega
          · simp only [if_neg clockZero] at run
            simp only [if_pos (show w.1 ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,clockZero⟩)]
            rcases bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL source) body with ⟨bodyResult,post⟩
            have bodyBound := bodyIH (decClockCrepSemHOL source) post bodyResult bodyRun
            have bodyClock := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL source) body
            rw [bodyRun] at bodyClock
            simp only [decClockCrepSemHOL] at bodyClock
            simp only [← hc] at *
            simp only [bodyRun] at run
            change source.clock - 1 - post.clock ≤ steps body (decClockCrepSemHOL source) at bodyBound
            have smaller : post.clock < source.clock := by omega
            cases bodyResult with
            | none =>
              have rest := ih post.clock smaller post final result run rfl
              simp only
              omega
            | some r =>
              cases r <;> try (simp_all [exitLoopCrepResult]; omega)
              case «break» label =>
                cases label <;> simp_all [exitLoopCrepResult] <;> omega
              case «continue» label =>
                cases label with
                | zero =>
                  have rest := ih post.clock smaller post final result run rfl
                  simp only
                  omega
                | succ n => simp_all [exitLoopCrepResult]; omega
        · simp only [if_neg nz,Prod.mk.injEq] at run
          obtain ⟨_,rfl⟩ := run
          simp only [nz,false_and,if_false]
          omega

end SteppedFlapjack.CrepSteps
