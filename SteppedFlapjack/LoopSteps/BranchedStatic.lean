import SteppedFlapjack.LoopToWordSteps.Conditional

/-! Static visit bounds for loop-free Loop programs with branches. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- Loop-free branch programs visit at most their syntax size. -/
theorem branchedProgram_static_bound {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : BranchedProgram p) (s : LoopSemStateFiniteExact width F) :
    steps p s ≤ sizeOf p := by
  induction shape generalizing s with
  | @leaf q leaf =>
    have one : steps q s = 1 := by
      apply steps_leaf
      cases leaf <;> rfl
    rw [one]
    cases leaf <;> simp_wf <;> omega
  | mark shape ih =>
    rw [steps_mark]
    have h := ih s
    simp_wf
    omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    have hfirst := iha s
    rcases evaluate a s with ⟨res,t⟩
    cases res with
    | none => have hsecond := ihb t; simp_wf; omega
    | some r => simp_wf; omega
  | @ite cmp r ri live a b ha hb iha ihb =>
    rw [steps_ite]
    have hfirst := iha s
    have hsecond := ihb s
    rcases sptLookup r s.locals with _ | (x | ⟨_,_⟩) <;> try (simp_wf; omega)
    rcases getVarImm ri s with _ | (y | ⟨_,_⟩) <;> try (simp_wf; omega)
    by_cases cmpResult : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true <;>
      simp only [cmpResult, if_true, Bool.false_eq_true, if_false] <;> simp_wf <;> omega

end SteppedFlapjack.LoopSteps
