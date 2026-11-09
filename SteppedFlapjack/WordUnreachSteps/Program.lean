import SteppedFlapjack.WordTwoRegSteps.Correct
import Flapjack.Compiler.Backend.WordUnreach.Proofs

/-! Unreachable-code removal on recursive call-free programs. -/
namespace SteppedFlapjack.WordUnreachSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordUnreach SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- The tail left after extracting a leading move remains in the supported
loop-sequence fragment. -/
theorem destSeqMove_shape {p rest : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (n : Nat) (moves : List (Nat × Nat)) (h : destSeqMove p = some (n,moves,rest)) : LoopSequence rest := by
  cases p with
  | move pri ms => simp [destSeqMove] at h; obtain ⟨_,_,rfl⟩ := h; exact .branch .skip
  | seq a b =>
    cases a <;> simp [destSeqMove] at h
    case move pri ms =>
      obtain ⟨_,_,rfl⟩ := h
      cases shape with
      | branch hp => cases hp with | seq ha hb => exact .branch hb
      | seq ha hb => exact hb
  | _ => simp [destSeqMove] at h

/-- Simplifying a sequence preserves the supported loop-sequence fragment. -/
theorem simpSeq_shape {a b : WordLangProgHOL (BitVec width)} (ha : LoopSequence a) (hb : LoopSequence b) :
    LoopSequence (simpSeq a b) := by
  unfold simpSeq
  by_cases skip : b = .skip
  · simp only [skip]
    exact ha
  · simp only [if_neg skip]
    cases a <;> try { exact .seq ha hb } <;> try { exact ha } <;> try { exact hb }
    case move pri ms =>
      cases h : destSeqMove b with
      | none => exact .seq ha hb
      | some value =>
        rcases value with ⟨n,moves,rest⟩
        have restShape := destSeqMove_shape hb n moves h
        by_cases endSkip : rest = .skip
        · simp only [endSkip]
          exact .branch (.move _ _)
        · simp only [if_neg endSkip]
          exact .seq (.branch (.move _ _)) restShape

/-- Extracting a leading move from a branch leaves a branch. -/
theorem destSeqMove_branch {p rest : WordLangProgHOL (BitVec width)} (shape : Branch p)
    (n : Nat) (moves : List (Nat × Nat)) (h : destSeqMove p = some (n,moves,rest)) : Branch rest := by
  cases p with
  | move pri ms => simp [destSeqMove] at h; obtain ⟨_,_,rfl⟩ := h; exact .skip
  | seq a b =>
    cases a <;> simp [destSeqMove] at h
    case move pri ms =>
      obtain ⟨_,_,rfl⟩ := h
      cases shape with | seq ha hb => exact hb
  | _ => simp [destSeqMove] at h

/-- Simplifying a sequence of branches yields a branch. -/
theorem simpSeq_branch {a b : WordLangProgHOL (BitVec width)} (ha : Branch a) (hb : Branch b) :
    Branch (simpSeq a b) := by
  unfold simpSeq
  by_cases skip : b = .skip
  · simp only [skip]; exact ha
  · simp only [if_neg skip]
    cases a <;> try { exact .seq ha hb } <;> try { exact ha } <;> try { exact hb }
    case move pri ms =>
      cases h : destSeqMove b with
      | none => exact .seq ha hb
      | some value =>
        rcases value with ⟨n,moves,rest⟩
        have restShape := destSeqMove_branch hb n moves h
        by_cases endSkip : rest = .skip
        · simp only [endSkip]; exact .move _ _
        · simp only [if_neg endSkip]; exact .seq (.move _ _) restShape

/-- Right-association keeps a branch loop-free. -/
theorem seqAssocRight_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    ∀ {acc : WordLangProgHOL (BitVec width)}, Branch acc → Branch (seqAssocRight p acc) := by
  induction shape with
  | skip => intro acc hacc; exact hacc
  | seq ha hb iha ihb => intro acc hacc; exact iha (ihb hacc)
  | ite cmp r ri ha hb iha ihb => intro acc hacc; exact simpSeq_branch (.ite cmp r ri (iha .skip) (ihb .skip)) hacc
  | assign dst e => intro acc hacc; exact simpSeq_branch (.assign dst e) hacc
  | inst i => intro acc hacc; exact simpSeq_branch (.inst i) hacc
  | move pri ms => intro acc hacc; exact simpSeq_branch (.move pri ms) hacc
  | get dst name => intro acc hacc; exact simpSeq_branch (.get dst name) hacc
  | opCurrHeap op dst src => intro acc hacc; exact simpSeq_branch (.opCurrHeap op dst src) hacc
  | set name e => intro acc hacc; exact simpSeq_branch (.set name e) hacc
  | store e src => intro acc hacc; exact simpSeq_branch (.store e src) hacc
  | tick => intro acc hacc; exact simpSeq_branch .tick hacc
  | ret r vs => intro acc hacc; exact simpSeq_branch (.ret r vs) hacc
  | «break» n => intro acc hacc; exact simpSeq_branch (.break n) hacc
  | «continue» n => intro acc hacc; exact simpSeq_branch (.continue n) hacc

/-- Right-association with unreachable removal preserves the fragment. -/
theorem seqAssocRight_shape {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ {acc : WordLangProgHOL (BitVec width)}, LoopSequence acc → LoopSequence (seqAssocRight p acc) := by
  induction shape with
  | branch hp =>
    intro acc hacc
    induction hp generalizing acc with
    | skip => exact hacc
    | seq ha hb iha ihb => exact iha (ihb hacc)
    | ite cmp r ri ha hb iha ihb =>
      simp only [seqAssocRight]
      exact simpSeq_shape (.branch (.ite cmp r ri (seqAssocRight_branch ha .skip) (seqAssocRight_branch hb .skip))) hacc
    | assign dst e => exact simpSeq_shape (.branch (.assign dst e)) hacc
    | inst i => exact simpSeq_shape (.branch (.inst i)) hacc
    | move pri ms => exact simpSeq_shape (.branch (.move pri ms)) hacc
    | get dst name => exact simpSeq_shape (.branch (.get dst name)) hacc
    | opCurrHeap op dst src => exact simpSeq_shape (.branch (.opCurrHeap op dst src)) hacc
    | set name e => exact simpSeq_shape (.branch (.set name e)) hacc
    | store e src => exact simpSeq_shape (.branch (.store e src)) hacc
    | tick => exact simpSeq_shape (.branch .tick) hacc
    | ret r vs => exact simpSeq_shape (.branch (.ret r vs)) hacc
    | «break» n => exact simpSeq_shape (.branch (.break n)) hacc
    | «continue» n => exact simpSeq_shape (.branch (.continue n)) hacc
  | nestedLoop names exits hp ih =>
    intro acc hacc
    simp only [seqAssocRight]
    exact simpSeq_shape (.nestedLoop names exits (ih (.branch .skip))) hacc
  | conditional cmp r ri ha hb iha ihb =>
    intro acc hacc
    simp only [seqAssocRight]
    exact simpSeq_shape (.conditional cmp r ri (iha (.branch .skip)) (ihb (.branch .skip))) hacc
  | loop names exits hp =>
    intro acc hacc
    simp only [seqAssocRight]
    exact simpSeq_shape (.loop names exits (seqAssocRight_branch hp .skip)) hacc
  | seq ha hb iha ihb =>
    intro acc hacc
    simp only [seqAssocRight]
    exact iha (ihb hacc)

/-- Actual unreachable removal preserves non-error execution and has an output
syntax-and-clock visit bound. -/
theorem removeUnreach_correct_with_steps {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (removeUnreach p) s = (res,post) ∧
    steps (removeUnreach p) s ≤ sizeOf (removeUnreach p) * (s.clock+1) :=
  ⟨evaluateRemoveUnreach p s res post ⟨run,nonerror⟩,
    loopSequence_clock_bound (seqAssocRight_shape shape (.branch .skip)) s⟩

end SteppedFlapjack.WordUnreachSteps
