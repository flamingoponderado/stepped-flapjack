import SteppedFlapjack.WordSimpSteps.TickLoop
import SteppedFlapjack.LoopToWordSteps.SelectedComposition

/-! Actual Loop-to-Word loops followed by WordSimp. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordSimpSteps

/-- Loop-free Loop code whose compiled Word body is covered by the WordSimp
branch proof. -/
inductive LoopBranch {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | skip : LoopBranch .skip
  | tick : LoopBranch .tick
  | assign (v e) : LoopBranch (.assign v e)
  | store (e v) : LoopBranch (.store e v)
  | setGlobal (v e) : LoopBranch (.setGlobal v e)
  | ret (vs) : LoopBranch (.return vs)
  | break (n) : LoopBranch (.break n)
  | continue (n) : LoopBranch (.continue n)
  | seq {a b} : LoopBranch a → LoopBranch b → LoopBranch (.seq a b)
  | mark {p} : LoopBranch p → LoopBranch (.mark p)
  | ite (cmp r ri live) {a b} : LoopBranch a → LoopBranch b → LoopBranch (.ite cmp r ri a b live)

theorem loopBranch_select {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopBranch p) : LoopSelectProgram p := by
  induction shape with
  | skip => exact .leaf .skip
  | tick => exact .leaf .tick
  | assign v e => exact .assign v e
  | store e v => exact .store e v
  | setGlobal v e => exact .leaf (.setGlobal v e)
  | ret vs => exact .leaf (.ret vs)
  | «break» n => exact .leaf (.break n)
  | «continue» n => exact .leaf (.continue n)
  | seq ha hb iha ihb => exact .seq iha ihb
  | mark ha ih => exact .mark ih
  | ite cmp r ri live ha hb iha ihb => exact .ite cmp r ri live iha ihb

/-- The exact compiled body belongs to the WordSimp branch fragment. -/
theorem loopBranch_word {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopBranch p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, Branch (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | skip => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .skip
  | tick => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .tick
  | assign v e => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .assign _ _
  | store e v => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .store _ _
  | setGlobal v e => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .set _ _
  | ret vs => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .ret _ _
  | «break» n => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .break _
  | «continue» n => intro labels; cases labels; simp only [LoopToWord.compHOL]; exact .continue _
  | seq ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt _ labels).2)
  | mark ha ih => intro labels; simpa only [LoopToWord.compHOL] using ih labels
  | @ite cmp r ri live a b ha hb iha ihb =>
    intro labels
    rcases h1 : LoopToWord.compHOL ctxt a labels with ⟨wa,la⟩
    rcases h2 : LoopToWord.compHOL ctxt b la with ⟨wb,lb⟩
    have hwa : Branch wa := by simpa only [h1] using iha labels
    have hwb : Branch wb := by simpa only [h2] using ihb la
    unfold LoopToWord.compHOL
    simp only [h1,h2]
    exact .seq (.ite _ _ _ hwa hwb) .tick

/-- A completed Loop execution bounds visits after the real Loop-to-Word and
WordSimp passes. -/
theorem loop_wordSimp_bound {F C : Type} (live exits : Spt Unit)
    {body : HolLoopProg 64} (shape : LoopBranch body)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (premises : evaluate (.loop live body exits) source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL (.loop live body exits) .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun) :
    ∃ wordPost wordResult,
      WordSemStateFiniteExact.evaluate (compileExp (LoopToWord.compHOL ctxt (.loop live body exits) labels).1) word = (wordResult,wordPost) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      WordSteps.steps (compileExp (LoopToWord.compHOL ctxt (.loop live body exits) labels).1) word ≤
        (3 + sizeOf (compileExp (LoopToWord.compHOL ctxt body labels).1)) * 6 * LoopSteps.steps (.loop live body exits) source := by
  have select : LoopSelectProgram (.loop live body exits) := .loop live exits (loopBranch_select shape)
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram select) source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,wordNonerror,_⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  refine ⟨wordPost,wordResult,?_,wordFfi,wordRel,?_⟩
  · apply (WordSemStateFiniteExact.compile_exp_thm _ word wordPost wordResult)
    constructor
    · exact wordRun
    · constructor
      · exact wordNonerror
      · exact gc
  · rcases hc : LoopToWord.compHOL ctxt body labels with ⟨wb,lb⟩
    have wbShape : Branch wb := by simpa only [hc] using loopBranch_word shape ctxt labels
    have bound := tick_loop_steps (LoopToWord.mkNewCutsetHOL ctxt live) (LoopToWord.mkNewCutsetHOL ctxt exits) wbShape word gc
    simp only [LoopToWord.compHOL,hc] at bound ⊢ wordBound
    nlinarith

/-- The optimized compiled loop is accepted by the existing instruction
selection proof, with no shape hypothesis on the generated Word code. -/
theorem loop_wordSimp_program {width : Nat} [NeZero width] (live exits : Spt Unit)
    {body : HolLoopProg width} (shape : LoopBranch body) (ctxt : Spt Nat) (labels : Nat × Nat) :
    WordInstSteps.Program (compileExp (LoopToWord.compHOL ctxt (.loop live body exits) labels).1) := by
  rcases hc : LoopToWord.compHOL ctxt body labels with ⟨wb,lb⟩
  have wordShape : Branch wb := by simpa only [hc] using loopBranch_word shape ctxt labels
  simp only [LoopToWord.compHOL,hc,compileExp_tick_loop]
  exact .seq (.seq .tick (.loop _ _ (branch_program (compileExp_branch wordShape)))) .tick

end SteppedFlapjack.LoopToWordSteps
