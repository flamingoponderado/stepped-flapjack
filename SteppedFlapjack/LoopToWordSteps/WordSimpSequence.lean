import SteppedFlapjack.LoopToWordSteps.WordSimpLoop
import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile

/-! WordSimp shape for Loop programs with loop-free initialization and tails. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps Flapjack.Compiler.Backend.WordSimp

/-- Sequences of Loop branches and loops whose bodies are branches. -/
inductive LoopSequenceSource {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | branch {p} : LoopBranch p → LoopSequenceSource p
  | loop (live exits) {body} : LoopBranch body → LoopSequenceSource (.loop live body exits)
  | seq {a b} : LoopSequenceSource a → LoopSequenceSource b → LoopSequenceSource (.seq a b)

/-- Loop-to-Word produces a supported Word sequence, including the ticks around
loops. -/
theorem loopSequenceSource_word {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSequenceSource p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, LoopSequence (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | branch h => intro labels; exact .branch (loopBranch_word h ctxt labels)
  | @loop live exits body hb =>
    intro labels
    rcases hc : LoopToWord.compHOL ctxt body labels with ⟨wb,lb⟩
    have wordShape : Branch wb := by simpa only [hc] using loopBranch_word hb ctxt labels
    simp only [LoopToWord.compHOL,hc]
    exact .seq (.branch .tick) (.seq (.loop _ _ wordShape) (.branch .tick))
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)

/-- The complete WordSimp output is ready for the existing instruction
selection proof for this source shape. -/
theorem loopSequenceSource_wordSimp_program {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSequenceSource p) (ctxt : Spt Nat) (labels : Nat × Nat) :
    WordInstSteps.Program (compileExp (LoopToWord.compHOL ctxt p labels).1) :=
  loopSequence_program (compileExp_loopSequence (loopSequenceSource_word shape ctxt labels))

end SteppedFlapjack.LoopToWordSteps
