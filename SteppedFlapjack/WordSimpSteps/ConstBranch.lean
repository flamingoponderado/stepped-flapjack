import SteppedFlapjack.WordSimpSteps.Branch

/-! Constant propagation preserves loop-free branch shape. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- Constant propagation transforms a branch into another branch, including
when known operands let it eliminate a conditional. -/
theorem constFpLoop_branch {p : WordLangProgHOL (BitVec width)} (hp : Branch p) :
    ∀ cs, Branch (constFpLoop p cs).1 := by
  induction hp with
  | assign dst e =>
    intro cs
    simp only [constFpLoop]
    split <;> exact .assign _ _
  | inst i => intro cs; exact .inst i
  | move pri ms => intro cs; exact .move pri ms
  | get dst n => intro cs; exact .get dst n
  | opCurrHeap op dst src => intro cs; exact .opCurrHeap op dst src
  | set n e => intro cs; exact .set n e
  | store e src => intro cs; exact .store _ src
  | skip => intro cs; exact .skip
  | tick => intro cs; exact .tick
  | ret r vs => intro cs; exact .ret r vs
  | «break» n => intro cs; exact .break n
  | «continue» n => intro cs; exact .continue n
  | seq ha hb iha ihb =>
    intro cs
    simp only [constFpLoop]
    rcases h : constFpLoop _ cs with ⟨a, ca⟩
    rcases k : constFpLoop _ ca with ⟨b, cb⟩
    have aa := iha cs
    have bb := ihb ca
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb
  | ite cmp r ri ha hb iha ihb =>
    intro cs
    simp only [constFpLoop]
    cases hx : sptLookup r cs <;> cases hy : getVarImmCs ri cs <;> simp only
    all_goals try {
      rcases h : constFpLoop _ cs with ⟨a, ca⟩
      rcases k : constFpLoop _ cs with ⟨b, cb⟩
      have aa := iha cs
      have bb := ihb cs
      simp only [h] at aa
      simp only [k] at bb
      exact .ite _ _ _ aa bb }
    split
    · exact iha cs
    · exact ihb cs

/-- Actual sequence normalization and constant propagation have a computable
source-relative visit bound for every loop-free branch. -/
theorem seqConst_branch_steps {p : WordLangProgHOL (BitVec width)} (hp : Branch p)
    (s : WordSemStateFiniteExact width C F) :
    steps (constFp (seqAssoc .skip p)) s ≤ sizeOf (constFp (seqAssoc .skip p)) * steps p s := by
  have shape : Branch (constFp (seqAssoc .skip p)) :=
    constFpLoop_branch (seqAssoc_branch hp .skip) .ln
  have h := branch_static shape s
  have positive := steps_pos p s
  nlinarith

/-- The first two WordSimp stages preserve a branch's evaluation under the
standard GC-function invariant, with the same computed visit bound. -/
theorem seqConst_branch_correct {p : WordLangProgHOL (BitVec width)} (hp : Branch p)
    (s : WordSemStateFiniteExact width C F) (gc : gcFunConstOk s.gcFun) :
    evaluate (constFp (seqAssoc .skip p)) s = evaluate p s ∧
    steps (constFp (seqAssoc .skip p)) s ≤ sizeOf (constFp (seqAssoc .skip p)) * steps p s := by
  exact ⟨(evaluate_const_fp _ s gc).trans (evaluate_Seq_assoc p s), seqConst_branch_steps hp s⟩

end SteppedFlapjack.WordSimpSteps
