import SteppedFlapjack.LoopToWordSteps.LoopProgram
import SteppedFlapjack.WordInstSteps.Compositional

/-! Relate Loop-to-Word output to the instruction-selection fragment. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordInstSteps

/-- Loop source programs supported by both quantitative passes. -/
inductive LoopSelectProgram {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : StackReadyLeaf p → LoopSelectProgram p
  | assign (v e) : LoopSelectProgram (.assign v e)
  | store (e v) : LoopSelectProgram (.store e v)
  | seq {a b} : LoopSelectProgram a → LoopSelectProgram b → LoopSelectProgram (.seq a b)
  | mark {p} : LoopSelectProgram p → LoopSelectProgram (.mark p)
  | ite (cmp r ri live) {a b} : LoopSelectProgram a → LoopSelectProgram b → LoopSelectProgram (.ite cmp r ri a b live)
  | loop (live liveOut) {p} : LoopSelectProgram p → LoopSelectProgram (.loop live p liveOut)

/-- The original quantitative Loop-to-Word theorem covers this fragment. -/
theorem loopSelect_loopProgram {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSelectProgram p) : LoopProgram p := by
  induction shape with
  | leaf h => exact .leaf (stackReadyLeaf_direct h)
  | assign v e => exact .leaf (.assign _ _)
  | store e v => exact .leaf (.store _ _)
  | seq _ _ ha hb => exact .seq ha hb
  | mark _ ih => exact .mark ih
  | ite cmp r ri live _ _ ha hb => exact .ite cmp r ri live ha hb
  | loop live liveOut _ ih => exact .loop live liveOut ih

/-- Actual Loop-to-Word output lies in the compositional instruction-selection
fragment, including assignments and stores that require instruction selection. -/
theorem loopSelect_wordProgram {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSelectProgram p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, Program (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | leaf h =>
    intro labels
    cases labels
    cases h <;> try { simp only [LoopToWord.compHOL]; constructor }
    case arith a => cases a <;> simp only [LoopToWord.compHOL] <;> constructor
  | assign v e => intro labels; simp only [LoopToWord.compHOL]; constructor
  | store e v => intro labels; simp only [LoopToWord.compHOL]; constructor
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)
  | mark h ih => intro labels; simpa only [LoopToWord.compHOL] using ih labels
  | @ite cmp r ri live a b ha hb iha ihb =>
    intro labels
    rcases h1 : LoopToWord.compHOL ctxt a labels with ⟨wa,la⟩
    rcases h2 : LoopToWord.compHOL ctxt b la with ⟨wb,lb⟩
    have hwa : Program wa := by simpa only [h1] using iha labels
    have hwb : Program wb := by simpa only [h2] using ihb la
    unfold LoopToWord.compHOL
    simp only [h1,h2]
    exact .seq (.ite _ _ _ hwa hwb) .tick
  | @loop live liveOut p hp ih =>
    intro labels
    rcases hc : LoopToWord.compHOL ctxt p labels with ⟨wordBody,next⟩
    have hword : Program wordBody := by simpa only [hc] using ih labels
    unfold LoopToWord.compHOL
    simp only [hc]
    exact .seq .tick (.seq (.loop _ _ hword) .tick)

end SteppedFlapjack.LoopToWordSteps
