import SteppedFlapjack.LoopToWordSteps.Conditional
import Flapjack.Pancake.CrepToLoop.Proofs.LoopEvaluateHelpers

/-! Stability of Loop step counts when a completed run gets more clock. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- Adding clock preserves the visited-node count for non-timeout runs of
Loop programs made from direct leaves, sequencing, marks and branches. -/
theorem branchedProgram_steps_add_clock {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : BranchedProgram p)
    (s final : LoopSemStateFiniteExact width F) (res : Option (LoopResultExact width))
    (run : evaluate p s = (res,final)) (nonTimeout : res ≠ some .timeOut) (extra : Nat) :
    steps p {s with clock := s.clock + extra} = steps p s := by
  induction shape generalizing s final res with
  | @leaf q leaf =>
    have h : ∀ t : LoopSemStateFiniteExact width F, steps q t = 1 := by
      intro t
      apply steps_leaf
      cases leaf <;> rfl
    rw [h,h]
  | mark shape ih =>
    rw [steps_mark,steps_mark]
    apply congrArg (Nat.add 1)
    apply ih s final res
    · simpa only [evaluate] using run
    · exact nonTimeout
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

end SteppedFlapjack.LoopSteps
