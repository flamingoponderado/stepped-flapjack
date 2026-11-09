import SteppedFlapjack.WordSimpSteps.LoopSequence

/-! Conditional hoisting for sequences that may contain loops. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width]

/-- Instructions the hoister may move across are loop-free branches. -/
theorem isSimple_branch (p : WordLangProgHOL (BitVec width)) (h : isSimple p = true) : Branch p := by
  cases p <;> simp_all [isSimple] <;> constructor

omit [NeZero width] in
/-- Inverting the recursive shape exposes both conditional arms. -/
theorem loopSequence_ite_inv (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (h : LoopSequence (.ite cmp r ri a b)) :
    LoopSequence a ∧ LoopSequence b := by
  cases h with
  | branch h => cases h with | ite _ _ _ ha hb => exact ⟨.branch ha,.branch hb⟩
  | conditional _ _ _ ha hb => exact ⟨ha,hb⟩

omit [NeZero width] in
/-- Inverting the recursive shape exposes both sequence components. -/
theorem loopSequence_seq_inv (a b : WordLangProgHOL (BitVec width))
    (h : LoopSequence (.seq a b)) : LoopSequence a ∧ LoopSequence b := by
  cases h with
  | branch h => cases h with | seq ha hb => exact ⟨.branch ha,.branch hb⟩
  | seq ha hb => exact ⟨ha,hb⟩

/-- Constant propagation preserves the recursive fragment. -/
theorem constFp_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    LoopSequence (constFp p) := by
  exact constFpLoop_loopSequence hp .ln

/-- Successful duplicate-conditional hoisting preserves recursive control flow. -/
theorem tryIfHoist2_loopSequence (fuel : Nat) : ∀
    {p interm dummy after out : WordLangProgHOL (BitVec width)},
    LoopSequence p → LoopSequence interm → LoopSequence after →
    tryIfHoist2 fuel p interm dummy after = some out → LoopSequence out := by
  induction fuel with
  | zero => intros; simp_all [tryIfHoist2]
  | succ fuel ih =>
    intro p interm dummy after out hp hi ht h
    cases p <;> try { simp [tryIfHoist2] at h }
    case ite cmp lhs rhs a b =>
      obtain ⟨ha,hb⟩ := loopSequence_ite_inv cmp lhs rhs a b hp
      simp only [tryIfHoist2] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · cases h
          exact constFp_loopSequence (.conditional cmp lhs rhs (.seq (.seq ha hi) ht) (.seq (.seq hb hi) ht))
    case seq a b =>
      obtain ⟨ha,hb⟩ := loopSequence_seq_inv a b hp
      simp only [tryIfHoist2] at h
      cases hd : destIf b with
      | none =>
        simp only [hd] at h
        split at h
        · rename_i simple
          exact ih ha (.seq (.branch (isSimple_branch b simple)) hi) ht h
        · contradiction
      | some value =>
        rcases value with ⟨cmp,lhs,rhs,x,y⟩
        have eq := (dest_If_thm _ cmp lhs rhs x y).mp hd
        subst b
        obtain ⟨hx,hy⟩ := loopSequence_ite_inv cmp lhs rhs x y hb
        simp only [hd] at h
        split at h
        · contradiction
        · split at h
          · contradiction
          · cases h
            exact .seq ha (constFp_loopSequence (.conditional cmp lhs rhs (.seq (.seq hx hi) ht) (.seq (.seq hy hi) ht)))

/-- The hoisting entry point cannot introduce unsupported loops. -/
theorem tryIfHoist1_loopSequence {a b out : WordLangProgHOL (BitVec width)}
    (ha : LoopSequence a) (hb : LoopSequence b) (h : tryIfHoist1 a b = some out) : LoopSequence out := by
  unfold tryIfHoist1 at h
  cases hd : destIf b with
  | none => simp [hd] at h
  | some value =>
    rcases value with ⟨cmp,lhs,rhs,x,y⟩
    have eq := (dest_If_thm _ cmp lhs rhs x y).mp hd
    subst b
    have parts := loopSequence_ite_inv cmp lhs rhs x y hb
    simp only [hd] at h
    exact tryIfHoist2_loopSequence _ ha (.branch .skip) (.conditional cmp lhs rhs parts.1 parts.2) h

/-- Duplicate-conditional simplification preserves programs with loop-free
initialization, loop bodies and continuations. -/
theorem simpDuplicateIf_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    LoopSequence (simpDuplicateIf p) := by
  induction hp with
  | branch hp => exact .branch (simpDuplicateIf_branch hp)
  | loop names exits hb => exact .loop names exits (simpDuplicateIf_branch hb)
  | nestedLoop names exits hb ih => exact .nestedLoop names exits ih
  | conditional cmp r ri ha hb iha ihb => exact .conditional cmp r ri iha ihb
  | @seq a b ha hb iha ihb =>
    simp only [simpDuplicateIf]
    cases h : tryIfHoist1 (simpDuplicateIf a) (simpDuplicateIf b) with
    | none => exact .seq iha ihb
    | some out => exact seqAssoc_loopSequence (tryIfHoist1_loopSequence iha ihb h) (.branch .skip)

end SteppedFlapjack.WordSimpSteps
