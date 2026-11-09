import SteppedFlapjack.WordSimpSteps.CompileLoop

/-! Sequences of bounded branches and loops in WordSimp. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width]

/-- Call-free programs with supported branches and recursive control flow. -/
inductive LoopSequence : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : Branch p → LoopSequence p
  | loop (names exits) {body} : Branch body → LoopSequence (.loop names body exits)
  | seq {a b} : LoopSequence a → LoopSequence b → LoopSequence (.seq a b)
  | nestedLoop (names exits) {body} : LoopSequence body → LoopSequence (.loop names body exits)
  | conditional (cmp r ri) {a b} : LoopSequence a → LoopSequence b → LoopSequence (.ite cmp r ri a b)

/-- Smart sequence elimination preserves programs with loops. -/
theorem smartSeq_loopSequence {a b : WordLangProgHOL (BitVec width)}
    (ha : LoopSequence a) (hb : LoopSequence b) : LoopSequence (Compiler.Backend.WordSimp.smartSeqHOL a b) := by
  cases a <;> simp only [Compiler.Backend.WordSimp.smartSeqHOL] <;> first | exact hb | exact .seq ha hb

/-- The actual sequence normalization preserves loop bodies and surrounding
initialization and continuation branches. -/
theorem seqAssoc_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    ∀ {prelude : WordLangProgHOL (BitVec width)}, LoopSequence prelude → LoopSequence (seqAssoc prelude p) := by
  induction hp with
  | branch hp =>
    intro prelude hprefix
    induction hp generalizing prelude with
    | skip => simpa only [Compiler.Backend.WordSimp.seqAssoc] using hprefix
    | seq ha hb iha ihb => simp only [Compiler.Backend.WordSimp.seqAssoc]; exact ihb (iha hprefix)
    | ite cmp r ri ha hb iha ihb =>
      simp only [Compiler.Backend.WordSimp.seqAssoc]
      exact smartSeq_loopSequence hprefix (.branch (.ite cmp r ri (seqAssoc_branch ha .skip) (seqAssoc_branch hb .skip)))
    | assign dst e => exact smartSeq_loopSequence hprefix (.branch (.assign dst e))
    | inst i => exact smartSeq_loopSequence hprefix (.branch (.inst i))
    | move pri ms => exact smartSeq_loopSequence hprefix (.branch (.move pri ms))
    | get dst n => exact smartSeq_loopSequence hprefix (.branch (.get dst n))
    | opCurrHeap op dst src => exact smartSeq_loopSequence hprefix (.branch (.opCurrHeap op dst src))
    | set n e => exact smartSeq_loopSequence hprefix (.branch (.set n e))
    | store e src => exact smartSeq_loopSequence hprefix (.branch (.store e src))
    | tick => exact smartSeq_loopSequence hprefix (.branch .tick)
    | ret r vs => exact smartSeq_loopSequence hprefix (.branch (.ret r vs))
    | «break» n => exact smartSeq_loopSequence hprefix (.branch (.break n))
    | «continue» n => exact smartSeq_loopSequence hprefix (.branch (.continue n))
  | loop names exits hbody =>
    intro prelude hprefix
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact smartSeq_loopSequence hprefix (.loop names exits (seqAssoc_branch hbody .skip))
  | nestedLoop names exits hbody ih =>
    intro prelude hprefix
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact smartSeq_loopSequence hprefix (.nestedLoop names exits (ih (.branch .skip)))
  | conditional cmp r ri ha hb iha ihb =>
    intro prelude hprefix
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact smartSeq_loopSequence hprefix (.conditional cmp r ri (iha (.branch .skip)) (ihb (.branch .skip)))
  | seq ha hb iha ihb =>
    intro prelude hprefix
    simp only [Compiler.Backend.WordSimp.seqAssoc]
    exact ihb (iha hprefix)

/-- Constant propagation keeps every loop body in the bounded branch fragment,
including when a preceding initialization branch establishes constants. -/
theorem constFpLoop_loopSequence {p : WordLangProgHOL (BitVec width)} (hp : LoopSequence p) :
    ∀ cs, LoopSequence (constFpLoop p cs).1 := by
  induction hp with
  | branch hp => intro cs; exact .branch (constFpLoop_branch hp cs)
  | loop names exits hp => intro cs; exact .loop names exits (constFpLoop_branch hp .ln)
  | nestedLoop names exits hb ih =>
    intro cs
    simpa only [constFpLoop] using LoopSequence.nestedLoop names exits (ih .ln)
  | conditional cmp r ri ha hb iha ihb =>
    intro cs
    simp only [constFpLoop]
    split
    · split
      · exact iha cs
      · exact ihb cs
    · exact .conditional cmp r ri (iha cs) (ihb cs)
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

end SteppedFlapjack.WordSimpSteps
