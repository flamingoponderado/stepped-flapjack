import SteppedFlapjack.WordSimpSteps.LoopSequenceHoist
import SteppedFlapjack.WordSimpSteps.Selection

/-! WordSimp output for sequences of branches and loops. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Conditional push-out keeps loops and their surrounding sequences in the
supported fragment. -/
theorem pushOutIfAux_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    LoopSequence (pushOutIfAux p).1 := by
  induction hp with
  | branch hp => exact .branch (pushOutIfAux_branch hp)
  | loop names exits hb => exact .loop names exits (pushOutIfAux_branch hb)
  | @seq a b ha hb iha ihb =>
    simp only [pushOutIfAux]
    rcases h : pushOutIfAux a with ⟨a',ba⟩
    simp only [h] at iha
    cases ba with
    | true => exact .seq iha hb
    | false =>
      rcases k : pushOutIfAux b with ⟨b',bb⟩
      simp only [k] at ihb
      exact .seq iha ihb

/-- All four stages of WordSimp preserve sequences of supported branches and
loops with branch bodies. -/
theorem compileExp_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    LoopSequence (compileExp p) := by
  apply pushOutIfAux_loopSequence
  apply simpDuplicateIf_loopSequence
  apply constFpLoop_loopSequence
  exact seqAssoc_loopSequence hp (.branch .skip)

/-- The transformed program is accepted by the existing instruction-selection
and Word-to-Stack structural proofs. -/
theorem loopSequence_program {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) : Program p := by
  induction hp with
  | branch hp => exact branch_program hp
  | loop names exits hp => exact .loop names exits (branch_program hp)
  | seq ha hb iha ihb => exact .seq iha ihb

/-- WordSimp's output shape and evaluation are derived from the input shape;
no hypothesis about the transformed program is needed. -/
theorem compileExp_loopSequence_correct {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) (gc : gcFunConstOk s.gcFun) :
    Program (compileExp p) ∧ evaluate (compileExp p) s = evaluate p s := by
  refine ⟨loopSequence_program (compileExp_loopSequence hp), ?_⟩
  simp only [Compiler.Backend.WordSimp.compileExp]
  rw [evaluate_simp_push_out_if, evaluate_simp_duplicate_if _ _ gc,
    evaluate_const_fp _ _ gc, evaluate_Seq_assoc]

end SteppedFlapjack.WordSimpSteps
