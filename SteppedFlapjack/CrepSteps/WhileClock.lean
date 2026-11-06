import SteppedFlapjack.CrepSteps.BranchClock

/-! Source clock consumption for loops with branch-program bodies. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack
open SteppedFlapjack.CrepToLoopSteps

/-- A Crep while loop consumes no more source clock than its actual visits. -/
theorem while_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (body : CrepProgHOL width) (shape : BranchProgram body)
    (source final : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (run : evalCrepSemHOLProgExact source (.while condition body) = (result,final)) :
    source.clock - final.clock ≤ steps (.while condition body) source := by
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
          have bodyBound := branchProgram_clock_consumed shape (decClockCrepSemHOL source) post bodyResult bodyRun
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
