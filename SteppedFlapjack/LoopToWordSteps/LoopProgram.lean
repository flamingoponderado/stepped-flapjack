import SteppedFlapjack.LoopToWordSteps.LoopBound
import SteppedFlapjack.LoopToWordSteps.ConditionalStack

/-! Close the quantitative loop induction over syntax. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord.CompileCorrect
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.WordToStackSteps

/-- Direct statements closed under sequences, branches, marks and loops. -/
inductive LoopProgram {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : LoopSteps.DirectLeaf p → LoopProgram p
  | seq {a b} : LoopProgram a → LoopProgram b → LoopProgram (.seq a b)
  | mark {p} : LoopProgram p → LoopProgram (.mark p)
  | ite (cmp r ri live) {a b} : LoopProgram a → LoopProgram b → LoopProgram (.ite cmp r ri a b live)
  | loop (live liveOut) {p} : LoopProgram p → LoopProgram (.loop live p liveOut)

/-- Semantic correctness and the sixfold bound hold for the entire fragment,
including nested loops, without a simulation hypothesis. -/
theorem loopProgram_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    {p : HolLoopProg width} (shape : LoopProgram p) :
    ∀ source : LoopSemStateFiniteExact width F, SixBoundPropertyAt C p source := by
  induction shape with
  | leaf leaf =>
    intro source result sourcePost target ctxt retv labels premises
    obtain ⟨targetPost,targetResult,run,ffi,relation,exactSteps⟩ :=
      LoopSteps.directLeaf_correct_with_steps _ leaf source sourcePost result target ctxt retv labels premises
    exact ⟨targetPost,targetResult,run,ffi,relation,by omega⟩
  | seq ha hb iha ihb =>
    intro source
    apply sixBoundedSeq _ _ source
    exact ⟨fun _ middle _ => ihb middle,iha source⟩
  | mark hp ih =>
    intro source
    exact sixBoundedMark _ source (ih source)
  | ite cmp r ri live ha hb iha ihb =>
    intro source
    apply sixBoundedIf cmp r ri _ _ live source
    intro v2 v3 v5 x v13 y b h1 h2 h3 h4 h5 h6
    cases b <;> simp only [Bool.false_eq_true,↓reduceIte]
    · exact ihb source
    · exact iha source
  | loop live liveOut hp ih =>
    exact sixBoundedLoop live liveOut _ ih

/-- The subset also supported by the existing Word-to-Stack loop proof. -/
inductive LoopStackReady {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : StackReadyLeaf p → LoopStackReady p
  | seq {a b} : LoopStackReady a → LoopStackReady b → LoopStackReady (.seq a b)
  | mark {p} : LoopStackReady p → LoopStackReady (.mark p)
  | ite (cmp r ri live) {a b} : LoopStackReady a → LoopStackReady b → LoopStackReady (.ite cmp r ri a b live)
  | loop (live liveOut) {p} : LoopStackReady p → LoopStackReady (.loop live p liveOut)

theorem loopStackReady_program {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopStackReady p) : LoopProgram p := by
  induction shape with
  | leaf h => exact .leaf (stackReadyLeaf_direct h)
  | seq _ _ ha hb => exact .seq ha hb
  | mark _ h => exact .mark h
  | ite cmp r ri live _ _ ha hb => exact .ite cmp r ri live ha hb
  | loop live liveOut _ h => exact .loop live liveOut h

/-- Actual Loop-to-Word compiler output fits the proved Stack block fragment. -/
theorem loopStackReady_wordBlock {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopStackReady p) (ctxt : Spt Nat) :
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
  | @loop live liveOut p hp ih =>
    intro labels
    rcases hc : LoopToWord.compHOL ctxt p labels with ⟨wordBody,next⟩
    have hword : LoopBlock wordBody := by simpa only [hc] using ih labels
    unfold LoopToWord.compHOL
    simp only [hc]
    exact .seq .tick (.seq (.loop _ _ hword) .tick)

/-- No dynamic installation is introduced by this source fragment. -/
theorem loopStackReady_noInstall {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopStackReady p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, noInstallSubprogsHOL (LoopToWord.compHOL ctxt p labels).1 = true := by
  induction shape with
  | leaf h => exact stackReady_noInstall (.leaf h) ctxt
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨iha labels,ihb (LoopToWord.compHOL ctxt a labels).2⟩
  | mark h ih =>
    intro labels
    simpa only [LoopToWord.compHOL] using ih labels
  | @ite cmp r ri live a b ha hb iha ihb =>
    intro labels
    rcases h1 : LoopToWord.compHOL ctxt a labels with ⟨wa,la⟩
    rcases h2 : LoopToWord.compHOL ctxt b la with ⟨wb,lb⟩
    have hwa : noInstallSubprogsHOL wa = true := by simpa only [h1] using iha labels
    have hwb : noInstallSubprogsHOL wb = true := by simpa only [h2] using ihb la
    unfold noInstallSubprogsHOL at hwa hwb
    unfold LoopToWord.compHOL
    simp [h1,h2,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,hwa,hwb]
  | @loop live liveOut p hp ih =>
    intro labels
    rcases hc : LoopToWord.compHOL ctxt p labels with ⟨wordBody,next⟩
    have hword : noInstallSubprogsHOL wordBody = true := by simpa only [hc] using ih labels
    unfold noInstallSubprogsHOL at hword
    unfold LoopToWord.compHOL
    simp [hc,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,hword]

end SteppedFlapjack.LoopToWordSteps
