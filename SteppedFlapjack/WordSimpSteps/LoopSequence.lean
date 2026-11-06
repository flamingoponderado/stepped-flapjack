import SteppedFlapjack.WordSimpSteps.CompileLoop

/-! Sequences of bounded branches and loops in WordSimp. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width]

/-- A call-free sequence of loop-free branches and loops with branch bodies. -/
inductive LoopSequence : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : Branch p → LoopSequence p
  | loop (names exits) {body} : Branch body → LoopSequence (.loop names body exits)
  | seq {a b} : LoopSequence a → LoopSequence b → LoopSequence (.seq a b)

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
