import SteppedFlapjack.WordInstSteps.Expression
import Flapjack.Compiler.Backend.WordSimp.Proofs.SeqAssoc

/-! Quantitative facts for the sequence transformations in WordSimp. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- Eliminating a leading skip never increases the number of Word visits. -/
theorem smartSeq_steps_le (a b : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    steps (Compiler.Backend.WordSimp.smartSeqHOL a b) s ≤ steps (.seq a b) s := by
  cases a <;> simp only [Compiler.Backend.WordSimp.smartSeqHOL] <;> try exact Nat.le_refl _
  rw [steps_seq, steps_leaf (.skip : WordLangProgHOL (BitVec width)) s rfl, evaluate_skip_eq]
  simp only
  omega

/-- Reassociating a sequence to the left adds at most one visited node; a result
from the first component can skip the right-associated inner sequence. -/
theorem seq_assoc_steps_le (a b c : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    steps (.seq (.seq a b) c) s ≤ steps (.seq a (.seq b c)) s + 1 := by
  rw [steps_seq, steps_seq, steps_seq, evaluate_seq_eq]
  rcases ha : evaluate a s with ⟨ra, sa⟩
  cases ra with
  | none =>
    simp only
    rw [steps_seq]
    rcases hb : evaluate b sa with ⟨rb, sb⟩
    cases rb <;> simp only <;> omega
  | some r => simp only; omega

/-- Reassociation to the right does not increase visits. -/
theorem seq_assoc_steps_ge (a b c : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    steps (.seq a (.seq b c)) s ≤ steps (.seq (.seq a b) c) s := by
  rw [steps_seq, steps_seq, steps_seq, evaluate_seq_eq]
  rcases ha : evaluate a s with ⟨ra, sa⟩
  cases ra with
  | none =>
    simp only
    rw [steps_seq]
    rcases hb : evaluate b sa with ⟨rb, sb⟩
    cases rb <;> simp only <;> omega
  | some r => simp only; omega

open SteppedFlapjack.WordInstSteps

/-- Smart sequencing preserves straight-line code. -/
theorem smartSeq_straight {a b : WordLangProgHOL (BitVec width)}
    (ha : Straight a) (hb : Straight b) : Straight (Compiler.Backend.WordSimp.smartSeqHOL a b) := by
  cases ha with
  | skip => exact hb
  | inst i => exact .seq (.inst i) hb
  | move priority moves => exact .seq (.move priority moves) hb
  | get dst name => exact .seq (.get dst name) hb
  | setVar name src => exact .seq (.setVar name src) hb
  | opCurrHeap op dst src => exact .seq (.opCurrHeap op dst src) hb
  | seq ha hc => exact .seq (.seq ha hc) hb

/-- The actual WordSimp sequence normalizer preserves straight-line code. -/
theorem seqAssoc_straight {b : WordLangProgHOL (BitVec width)} (hb : Straight b) :
    ∀ {a : WordLangProgHOL (BitVec width)}, Straight a → Straight (Compiler.Backend.WordSimp.seqAssoc a b) := by
  induction hb with
  | skip => intro a ha; simpa [Compiler.Backend.WordSimp.seqAssoc] using ha
  | seq hb hc ihb ihc =>
    intro a ha
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact ihc (ihb ha)
  | inst i => intro a ha; exact smartSeq_straight ha (.inst i)
  | move priority moves => intro a ha; exact smartSeq_straight ha (.move priority moves)
  | get dst name => intro a ha; exact smartSeq_straight ha (.get dst name)
  | setVar name src => intro a ha; exact smartSeq_straight ha (.setVar name src)
  | opCurrHeap op dst src => intro a ha; exact smartSeq_straight ha (.opCurrHeap op dst src)

/-- A straight-line fragment after actual sequence normalization has the same
Word evaluation and a calculable bound on its evaluator visits. -/
theorem seqAssoc_straight_correct {p : WordLangProgHOL (BitVec width)}
    (hp : Straight p) (s : WordSemStateFiniteExact width C F) :
    evaluate (Compiler.Backend.WordSimp.seqAssoc .skip p) s = evaluate p s ∧
    steps (Compiler.Backend.WordSimp.seqAssoc .skip p) s ≤ sizeOf (Compiler.Backend.WordSimp.seqAssoc .skip p) := by
  exact ⟨evaluate_Seq_assoc p s, straight_steps_bound (seqAssoc_straight hp .skip) s⟩

/-- The normalized visits are bounded by a computed syntax factor times the
original visits. This holds for arbitrary source states, including early exits. -/
theorem seqAssoc_straight_steps {p : WordLangProgHOL (BitVec width)}
    (hp : Straight p) (s : WordSemStateFiniteExact width C F) :
    steps (Compiler.Backend.WordSimp.seqAssoc .skip p) s ≤
      sizeOf (Compiler.Backend.WordSimp.seqAssoc .skip p) * steps p s := by
  have bound := (seqAssoc_straight_correct hp s).2
  have positive := steps_pos p s
  nlinarith

end SteppedFlapjack.WordSimpSteps
