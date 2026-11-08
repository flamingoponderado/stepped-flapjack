import SteppedFlapjack.LoopLiveSteps.ClockBound
import SteppedFlapjack.CrepToLoopSteps.ScalarLoop
import SteppedFlapjack.LoopSteps.BranchedClock
import SteppedFlapjack.LoopSteps.IterationClock

/-! Clock-shift invariance for recursively nested scalar Loop programs. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps

theorem scalarLoop_steps_add_clock {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : ScalarLoop p)
    (s final : LoopSemStateFiniteExact width F) (res : Option (LoopResultExact width))
    (run : evaluate p s = (res,final)) (nonTimeout : res ≠ some .timeOut) (extra : Nat) :
    steps p {s with clock := s.clock + extra} = steps p s := by
  induction shape generalizing s final res with
  | branch h => exact branchedProgram_steps_add_clock (SteppedFlapjack.LoopLiveSteps.branch_branched h) s final res run nonTimeout extra
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,steps_seq]
    rcases firstRun : evaluate a s with ⟨firstRes,middle⟩
    have firstNotTimeout : firstRes ≠ some .timeOut := by
      intro bad
      have whole := run
      rw [evaluate_seq,firstRun,bad] at whole
      cases whole
      exact nonTimeout rfl
    have firstLift := evaluate_add_clock_eq a s firstRes middle extra firstRun firstNotTimeout
    rw [firstLift]
    have firstSteps := iha s middle firstRes firstRun firstNotTimeout
    rw [firstSteps]
    cases firstRes with
    | some r => rfl
    | none =>
      have secondRun : evaluate b middle = (res,final) := by
        rw [evaluate_seq,firstRun] at run
        exact run
      have secondSteps := ihb middle final res secondRun nonTimeout
      simpa only using congrArg (fun n => 1 + steps a s + n) secondSteps

  | @ite cmp r ri live a b ha hb iha ihb =>
    rw [steps_ite,steps_ite]
    have sameLookup : sptLookup r ({s with clock := s.clock + extra} : LoopSemStateFiniteExact width F).locals =
        sptLookup r s.locals := rfl
    have sameImm : getVarImm ri {s with clock := s.clock + extra} = getVarImm ri s := by
      cases ri <;> rfl
    rw [sameLookup,sameImm]
    rcases hx : sptLookup r s.locals with _ | (x | ⟨_,_⟩) <;> try rfl
    rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> try rfl
    simp only
    have run' := run
    simp only [evaluate,hx,hy] at run'
    by_cases compare : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
    · simp only [compare,if_true] at run' ⊢
      rcases branch : evaluate a s with ⟨branchResult,branchPost⟩
      have noTimeout : branchResult ≠ some .timeOut := by
        intro bad
        rw [branch,bad] at run'
        simp only [cutRes,Prod.mk.injEq] at run'
        exact nonTimeout run'.1.symm
      have bound := iha s branchPost branchResult branch noTimeout
      exact congrArg (Nat.add 1) bound
    · simp only [compare,Bool.false_eq_true,if_false] at run' ⊢
      rcases branch : evaluate b s with ⟨branchResult,branchPost⟩
      have noTimeout : branchResult ≠ some .timeOut := by
        intro bad
        rw [branch,bad] at run'
        simp only [cutRes,Prod.mk.injEq] at run'
        exact nonTimeout run'.1.symm
      have bound := ihb s branchPost branchResult branch noTimeout
      exact congrArg (Nat.add 1) bound

  | @loop live liveOut body bodyShape bodyIH =>
    induction hc : s.clock using Nat.strongRecOn generalizing s final res with
    | _ clock ih =>
      rcases cutRun : cutRes live (none,s) with ⟨cutResult,entry⟩
      cases cutResult with
      | some r =>
        have cutNotTimeout : some r ≠ some .timeOut := by
          intro bad
          have whole := run
          rw [evaluate,cutRun] at whole
          simp only at whole
          have : res = some r := (Prod.mk.inj whole).1.symm
          exact nonTimeout (this.trans bad)
        have cutShift := cutRes_add_clock live none s entry (some r) extra cutRun cutNotTimeout
        simp only [← hc]
        rw [steps_loop,steps_loop,cutRun,cutShift]
      | none =>
        rcases bodyRun : evaluate body entry with ⟨bodyResult,post⟩
        have entryClock := cutRes_none_clock cutRun
        have bodyClock := evaluate_clock body entry bodyResult post bodyRun
        have execution := run
        rw [evaluate,cutRun] at execution
        simp only at execution
        rw [fix_clock_evaluate,bodyRun] at execution
        have bodyNotTimeout : bodyResult ≠ some .timeOut := by
          intro bad
          rw [bad] at execution
          simp only [LoopSemStateFiniteExact.exitLoop,Prod.mk.injEq] at execution
          exact nonTimeout execution.1.symm
        have cutShift := cutRes_add_clock live none s entry none extra cutRun (by simp)
        have bodyShift := evaluate_add_clock_eq body entry bodyResult post extra bodyRun bodyNotTimeout
        have bodySteps := bodyIH entry post bodyResult bodyRun bodyNotTimeout
        simp only [← hc]
        rw [steps_loop,steps_loop,cutRun,cutShift]
        simp only
        rw [bodyRun,bodyShift,bodySteps]
        by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
        · have recurRun : evaluate (.loop live body liveOut) post = (res,final) := by
            rcases continuing with h | h <;> rw [h] at execution <;> exact execution
          have smaller : post.clock < clock := by omega
          have recur := ih post.clock smaller post final res recurRun nonTimeout rfl
          rcases continuing with h | h <;> rw [h] <;> simp only
          all_goals rw [recur]
        · cases bodyResult with
          | none => exact (continuing (Or.inl rfl)).elim
          | some r =>
            cases r <;> try rfl
            case «continue» label =>
              cases label with
              | zero => exact (continuing (Or.inr rfl)).elim
              | succ n => rfl

end SteppedFlapjack.CrepToLoopSteps
