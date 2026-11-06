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
/-- A conditional in the loop-sequence fragment has loop-free branches. -/
theorem loopSequence_ite_inv (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (h : LoopSequence (.ite cmp r ri a b)) : Branch a ∧ Branch b := by
  cases h with
  | branch h => cases h with | ite _ _ _ ha hb => exact ⟨ha,hb⟩

/-- Successful duplicate-conditional hoisting preserves the loop-sequence
fragment, including loops before the transformed conditional. -/
theorem tryIfHoist2_loopSequence (fuel : Nat) : ∀
    {p interm dummy after out : WordLangProgHOL (BitVec width)},
    LoopSequence p → Branch interm → Branch after →
    tryIfHoist2 fuel p interm dummy after = some out → LoopSequence out := by
  induction fuel with
  | zero => intros; simp_all [tryIfHoist2]
  | succ fuel ih =>
    intro p interm dummy after out hp hi ht h
    cases hp with
    | branch hp => exact .branch (tryIfHoist2_branch _ hp hi ht h)
    | loop names exits hb => simp [tryIfHoist2] at h
    | @seq a b ha hb =>
      simp only [tryIfHoist2] at h
      cases hd : destIf b with
      | none =>
        simp only [hd] at h
        split at h
        · rename_i simple
          exact ih ha (.seq (isSimple_branch b simple) hi) ht h
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
            exact .seq ha (.branch (constFp_branch (.ite cmp lhs rhs (.seq (.seq hx hi) ht) (.seq (.seq hy hi) ht))))

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
    exact tryIfHoist2_loopSequence _ ha .skip (.ite cmp lhs rhs parts.1 parts.2) h

/-- Duplicate-conditional simplification preserves programs with loop-free
initialization, loop bodies and continuations. -/
theorem simpDuplicateIf_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    LoopSequence (simpDuplicateIf p) := by
  induction hp with
  | branch hp => exact .branch (simpDuplicateIf_branch hp)
  | loop names exits hb => exact .loop names exits (simpDuplicateIf_branch hb)
  | @seq a b ha hb iha ihb =>
    simp only [simpDuplicateIf]
    cases h : tryIfHoist1 (simpDuplicateIf a) (simpDuplicateIf b) with
    | none => exact .seq iha ihb
    | some out => exact seqAssoc_loopSequence (tryIfHoist1_loopSequence iha ihb h) (.branch .skip)

end SteppedFlapjack.WordSimpSteps
