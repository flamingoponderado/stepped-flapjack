import SteppedFlapjack.WordUnreachSteps.Program
import SteppedFlapjack.WordTwoRegSteps.TailEntry

/-! Unreachable-code removal for direct tail entries. -/
namespace SteppedFlapjack.WordUnreachSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordUnreach
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordDeadSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

theorem destSeqMove_allowedTailEntry {allowed : Nat → Prop} {p rest : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) (n : Nat) (moves : List (Nat × Nat))
    (h : destSeqMove p = some (n,moves,rest)) : AllowedTailEntry allowed rest := by
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

theorem simpSeq_allowedTailEntry {allowed : Nat → Prop} {a b : WordLangProgHOL (BitVec width)}
    (ha : AllowedTailEntry allowed a) (hb : AllowedTailEntry allowed b) :
    AllowedTailEntry allowed (simpSeq a b) := by
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
        have restShape := destSeqMove_allowedTailEntry hb n moves h
        by_cases endSkip : rest = .skip
        · simp only [endSkip]; exact .branch (.move _ _)
        · simp only [if_neg endSkip]; exact .seq (.branch (.move _ _)) restShape

/-- Unreachable removal may remove calls, but cannot introduce destinations. -/
theorem seqAssocRight_allowedTailEntry {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : ∀ {acc}, AllowedTailEntry allowed acc →
      AllowedTailEntry allowed (seqAssocRight p acc) := by
  induction shape with
  | branch hp =>
    intro acc hacc
    induction hp generalizing acc with
    | skip => exact hacc
    | seq ha hb iha ihb => exact iha (ihb hacc)
    | ite cmp r ri ha hb iha ihb =>
      simp only [seqAssocRight]
      exact simpSeq_allowedTailEntry (.branch (.ite cmp r ri (seqAssocRight_branch ha .skip) (seqAssocRight_branch hb .skip))) hacc
    | assign dst e => exact simpSeq_allowedTailEntry (.branch (.assign dst e)) hacc
    | inst i => exact simpSeq_allowedTailEntry (.branch (.inst i)) hacc
    | move pri ms => exact simpSeq_allowedTailEntry (.branch (.move pri ms)) hacc
    | get dst name => exact simpSeq_allowedTailEntry (.branch (.get dst name)) hacc
    | opCurrHeap op dst src => exact simpSeq_allowedTailEntry (.branch (.opCurrHeap op dst src)) hacc
    | set name e => exact simpSeq_allowedTailEntry (.branch (.set name e)) hacc
    | store e src => exact simpSeq_allowedTailEntry (.branch (.store e src)) hacc
    | tick => exact simpSeq_allowedTailEntry (.branch .tick) hacc
    | ret r vs => exact simpSeq_allowedTailEntry (.branch (.ret r vs)) hacc
    | «break» n => exact simpSeq_allowedTailEntry (.branch (.break n)) hacc
    | «continue» n => exact simpSeq_allowedTailEntry (.branch (.continue n)) hacc
  | call loc good => intro acc hacc; exact .call loc good
  | seq ha hb iha ihb => intro acc hacc; simp only [seqAssocRight]; exact iha (ihb hacc)

/-- Actual unreachable removal preserves a non-error entry execution and
its direct-call code bound. -/
theorem removeUnreach_tailEntry_correct {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (K : Nat) (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    evaluate (removeUnreach p) s = (res,post) ∧ WordTailEntryShape (removeUnreach p) ∧
    TailEntryCodeBound (removeUnreach p) s.code K ∧
    WordSteps.steps (removeUnreach p) s ≤ sizeOf (removeUnreach p) * (K+1) * (s.clock+1) := by
  have init := tailEntry_allowed_of_code shape s.code K code
  have output := seqAssocRight_allowedTailEntry init (.branch .skip)
  have outShape : WordTailEntryShape (removeUnreach p) := allowedTailEntry_shape output
  have outCode : TailEntryCodeBound (removeUnreach p) s.code K := allowedTailEntry_calls output
  exact ⟨evaluateRemoveUnreach p s res post ⟨run,nonerror⟩,outShape,outCode,
    tailEntry_clock_bound outShape s K (tailEntry_noInstall outShape) noInstallCode outCode⟩

end SteppedFlapjack.WordUnreachSteps
