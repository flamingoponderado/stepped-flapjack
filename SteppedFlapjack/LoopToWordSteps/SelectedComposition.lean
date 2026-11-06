import SteppedFlapjack.LoopToWordSteps.SelectedShape

/-! Quantitative Loop-to-Word compilation followed by instruction selection. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordInstSteps

/-- A completed Loop run induces an instruction-selected Word run whose step
bound is the source count times a program-dependent selection factor. -/
theorem loopSelect_selectedWord_bound {C F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (p : HolLoopProg 64) (shape : LoopSelectProgram p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat)
    (labels : Nat × Nat) (locals : Spt (WordLocW 64))
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result)
    (vars : everyVarHOL (fun x => decide (x < temp)) (LoopToWord.compHOL ctxt p labels).1 = true)
    (localRel : wordLocalsRel temp word.locals locals) :
    ∃ wordResult wordPost selectedLocals,
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 word = (wordResult,wordPost) ∧
      WordSemStateFiniteExact.evaluate (instSelect ac temp (LoopToWord.compHOL ctxt p labels).1)
        {word with locals := locals} = (wordResult,{wordPost with locals := selectedLocals}) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      WordSteps.steps (instSelect ac temp (LoopToWord.compHOL ctxt p labels).1) {word with locals := locals} ≤
        (6 * programFactor ac temp (LoopToWord.compHOL ctxt p labels).1) * LoopSteps.steps p source := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram shape) source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,wordNonerror,_⟩ :=
    completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  obtain ⟨selectedLocals,selectedRun,_⟩ := inst_select_thm ac temp (LoopToWord.compHOL ctxt p labels).1
    word wordResult wordPost locals ⟨wordRun,vars,wordNonerror,localRel⟩
  have selectedBound := boundedProgram_steps (C := C) (F := F) ac temp
    (program_factor ac temp (loopSelect_wordProgram shape ctxt labels)) word wordPost wordResult locals
    wordRun wordNonerror vars localRel
  refine ⟨wordResult,wordPost,selectedLocals,wordRun,selectedRun,wordFfi,wordRel,?_⟩
  nlinarith

end SteppedFlapjack.LoopToWordSteps
