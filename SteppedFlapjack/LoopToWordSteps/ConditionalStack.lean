import SteppedFlapjack.LoopToWordSteps.Conditional
import SteppedFlapjack.LoopToWordSteps.StackReady

/-! Shared conditional Loop-to-Stack fragment. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact SteppedFlapjack.WordToStackSteps
open Flapjack.Compiler.Encoders.Asm

/-- Shared direct leaves, sequences, marks, and conditionals. -/
inductive BranchedStackReady {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : StackReadyLeaf p → BranchedStackReady p
  | seq {a b} : BranchedStackReady a → BranchedStackReady b → BranchedStackReady (.seq a b)
  | mark {p} : BranchedStackReady p → BranchedStackReady (.mark p)
  | ite (cmp r ri live) {a b} : BranchedStackReady a → BranchedStackReady b →
      BranchedStackReady (.ite cmp r ri a b live)

theorem branchedStackReady_program {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : BranchedStackReady p) : BranchedProgram p := by
  induction shape with
  | leaf h => exact .leaf (stackReadyLeaf_direct h)
  | seq _ _ ha hb => exact .seq ha hb
  | mark _ h => exact .mark h
  | ite cmp r ri live _ _ ha hb => exact .ite cmp r ri live ha hb

/-- The actual Word compiler output lies in the proved Word-to-Stack block fragment. -/
theorem branchedStackReady_wordBlock {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : BranchedStackReady p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, LoopBlock (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | leaf h => exact stackReadyLeaf_wordBlock h ctxt
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)
  | mark h ih =>
    intro labels
    simpa only [LoopToWord.compHOL] using ih labels
  | @ite cmp r ri live a b ha hb iha ihb =>
    intro labels
    rcases h1 : LoopToWord.compHOL ctxt a labels with ⟨wa,la⟩
    rcases h2 : LoopToWord.compHOL ctxt b la with ⟨wb,lb⟩
    have hwa : LoopBlock wa := by simpa only [h1] using iha labels
    have hwb : LoopBlock wb := by simpa only [h2] using ihb la
    unfold LoopToWord.compHOL
    simp only [h1,h2]
    exact .seq (.ite _ _ _ hwa hwb) .tick

end SteppedFlapjack.LoopToWordSteps
