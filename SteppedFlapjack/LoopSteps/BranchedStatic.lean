import SteppedFlapjack.LoopToWordSteps.Conditional

/-! Static visit bounds for loop-free Loop programs with branches. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- Counts Loop statements without counting literal values or names. -/
def structuralWeight {width : Nat} [NeZero width] : HolLoopProg width → Nat
  | .mark body => 1 + structuralWeight body
  | .seq a b => 1 + structuralWeight a + structuralWeight b
  | .ite _ _ _ a b _ => 1 + structuralWeight a + structuralWeight b
  | _ => 1

theorem branchedProgram_structural_bound {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : BranchedProgram p) (s : LoopSemStateFiniteExact width F) :
    steps p s ≤ structuralWeight p := by
  induction shape generalizing s with
  | @leaf q leaf =>
    have one : steps q s = 1 := by
      apply steps_leaf
      cases leaf <;> rfl
    rw [one]
    cases leaf <;> simp [structuralWeight]
  | mark shape ih =>
    rw [steps_mark]
    have h := ih s
    simp only [structuralWeight]
    omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    have hfirst := iha s
    rcases evaluate a s with ⟨res,t⟩
    cases res with
    | none => have hsecond := ihb t; simp only [structuralWeight]; omega
    | some r => simp only [structuralWeight]; omega
  | @ite cmp r ri live a b ha hb iha ihb =>
    rw [steps_ite]
    have hfirst := iha s
    have hsecond := ihb s
    rcases sptLookup r s.locals with _ | (x | ⟨_,_⟩) <;> try (simp only [structuralWeight]; omega)
    rcases getVarImm ri s with _ | (y | ⟨_,_⟩) <;> try (simp only [structuralWeight]; omega)
    by_cases cmpResult : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true <;>
      simp only [cmpResult, if_true, Bool.false_eq_true, if_false,structuralWeight] <;> omega


theorem branchedProgram_weight_le_size {width : Nat} [NeZero width]
    {p : HolLoopProg width} (shape : BranchedProgram p) :
    structuralWeight p ≤ sizeOf p := by
  induction shape with
  | @leaf q leaf => cases leaf <;> simp only [structuralWeight] <;> simp_wf <;> omega
  | mark shape ih => simp only [structuralWeight]; simp_wf; omega
  | seq a b iha ihb => simp only [structuralWeight]; simp_wf; omega
  | ite cmp r ri live a b iha ihb => simp only [structuralWeight]; simp_wf; omega

/-- Loop-free branch programs visit at most their syntax size. -/
theorem branchedProgram_static_bound {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : BranchedProgram p) (s : LoopSemStateFiniteExact width F) :
    steps p s ≤ sizeOf p :=
  Nat.le_trans (branchedProgram_structural_bound shape s) (branchedProgram_weight_le_size shape)

end SteppedFlapjack.LoopSteps
