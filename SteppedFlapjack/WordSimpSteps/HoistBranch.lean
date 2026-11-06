import SteppedFlapjack.WordSimpSteps.PushBranch

/-! Duplicate-conditional hoisting preserves loop-free branch shape. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

theorem constFp_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) : Branch (constFp p) :=
  constFpLoop_branch shape .ln

/-- If hoisting succeeds, the output remains a branch. -/
theorem tryIfHoist2_branch (fuel : Nat) : ∀
    {p interm dummy after out : WordLangProgHOL (BitVec width)},
    Branch p → Branch interm → Branch after →
    tryIfHoist2 fuel p interm dummy after = some out → Branch out := by
  induction fuel with
  | zero => intros; simp_all [tryIfHoist2]
  | succ fuel ih =>
    intro p interm dummy after out hp hi ht h
    cases hp with
    | ite cmp lhs rhs ha hb =>
      simp only [tryIfHoist2] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · cases h
          exact constFp_branch (.ite cmp lhs rhs (.seq (.seq ha hi) ht) (.seq (.seq hb hi) ht))
    | @seq a b ha hb =>
      simp only [tryIfHoist2] at h
      cases hd : destIf b with
      | none =>
        simp only [hd] at h
        split at h
        · exact ih ha (.seq hb hi) ht h
        · contradiction
      | some value =>
        rcases value with ⟨cmp,lhs,rhs,a,b⟩
        have eq := (dest_If_thm _ cmp lhs rhs a b).mp hd
        subst_vars
        cases hb with
        | ite _ _ _ h1 h2 =>
          simp only [hd] at h
          split at h
          · contradiction
          · split at h
            · contradiction
            · cases h
              exact .seq ha (constFp_branch (.ite cmp lhs rhs (.seq (.seq h1 hi) ht) (.seq (.seq h2 hi) ht)))
    | assign _ _ | inst _ | move _ _ | get _ _ | opCurrHeap _ _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
      simp [tryIfHoist2] at h

/-- The hoist entry point returns a branch whenever both inputs are branches. -/
theorem tryIfHoist1_branch {a b out : WordLangProgHOL (BitVec width)}
    (ha : Branch a) (hb : Branch b) (h : tryIfHoist1 a b = some out) : Branch out := by
  unfold tryIfHoist1 at h
  cases hd : destIf b with
  | none => simp [hd] at h
  | some value =>
    rcases value with ⟨cmp,lhs,rhs,x,y⟩
    simp only [hd] at h
    exact tryIfHoist2_branch _ ha .skip hb h

/-- The complete duplicate-conditional simplifier preserves branch shape. -/
theorem simpDuplicateIf_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    Branch (simpDuplicateIf p) := by
  induction shape with
  | assign dst e => exact .assign dst e
  | inst i => exact .inst i
  | move pri ms => exact .move pri ms
  | get dst n => exact .get dst n
  | opCurrHeap op dst src => exact .opCurrHeap op dst src
  | set n e => exact .set n e
  | store e src => exact .store e src
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret r vs
  | «break» n => exact .break n
  | «continue» n => exact .continue n
  | ite cmp lhs rhs ha hb iha ihb => exact .ite cmp lhs rhs iha ihb
  | @seq a b ha hb iha ihb =>
    simp only [simpDuplicateIf]
    cases h : tryIfHoist1 (simpDuplicateIf a) (simpDuplicateIf b) with
    | none => exact .seq iha ihb
    | some out => exact seqAssoc_branch (tryIfHoist1_branch iha ihb h) .skip

end SteppedFlapjack.WordSimpSteps
