import SteppedFlapjack.LoopToWordSteps.WordSimpSequence
import SteppedFlapjack.WordSimpSteps.LoopSequenceBound

/-! Loop-to-WordSimp visit bounds for sequences with loops. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps Flapjack.Compiler.Backend.WordSimp

theorem loopSequenceSource_select {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSequenceSource p) : LoopSelectProgram p := by
  induction shape with
  | branch h => exact loopBranch_select h
  | loop live exits h => exact .loop live exits (loopBranch_select h)
  | seq ha hb iha ihb => exact .seq iha ihb

/-- Shared Loop-to-Word execution and visit bound used by the Word-pass
compositions. Completion discharges error and timeout cases once here. -/
theorem loopSequence_word_execution {F C : Type}
    (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat)
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    ∃ wordPost wordResult,
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 word = (wordResult,wordPost) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordResult ≠ some .error ∧ wordResult ≠ some .timeOut ∧
      WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 word ≤ 6*limit := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram (loopSequenceSource_select shape))
      source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,nonerror,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  exact ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,nonerror,notTimeout,by omega⟩

/-- Compose the bounded Loop-to-Word execution with any Word prefix whose
correctness theorem supplies a related final state and a visit bound. Concrete
passes discharge `prefixCorrect` using their own proved correctness theorems. -/
theorem loopSequence_composeWordPrefix {F C : Type}
    (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (locals : Spt (WordLocW 64)) (limit : Nat) (output : WordLangProgHOL (BitVec 64))
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit)
    (prefixCorrect : ∀ wordPost wordResult,
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 word = (wordResult,wordPost) →
      wordResult ≠ some .error → wordResult ≠ some .timeOut →
      WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 word ≤ 6*limit →
      ∃ selectedLocals targetPost deadLocals,
        Flapjack.WordAlloc.wordStateEqRel
          {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
        WordSemStateFiniteExact.evaluate output {word with locals := locals,clock := 6*limit} =
          (wordResult,{targetPost with locals := deadLocals}) ∧
        WordSteps.steps output {word with locals := locals,clock := 6*limit} ≤ sizeOf output * (6*limit+1)) :
    ∃ wordPost wordResult selectedLocals targetPost deadLocals,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      Flapjack.WordAlloc.wordStateEqRel
        {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate output {word with locals := locals,clock := 6*limit} =
        (wordResult,{targetPost with locals := deadLocals}) ∧
      WordSteps.steps output {word with locals := locals,clock := 6*limit} ≤ sizeOf output * (6*limit+1) := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,nonerror,notTimeout,bound⟩ :=
    loopSequence_word_execution p shape source sourcePost result word ctxt labels limit premises complete sourceBound
  obtain ⟨selectedLocals,targetPost,deadLocals,rel,run,steps⟩ :=
    prefixCorrect wordPost wordResult wordRun nonerror notTimeout bound
  exact ⟨wordPost,wordResult,selectedLocals,targetPost,deadLocals,wordRel,wordFfi,rel,run,steps⟩

/-- A completed Loop program yields a normalized execution of its exact
Loop-to-Word and WordSimp output, with a visit bound derived from the Loop
source visits and a syntax factor. -/
theorem loopSequence_wordSimp_bound {F C : Type} (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat)
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    ∃ wordPost wordResult,
      WordSemStateFiniteExact.evaluate (compileExp (LoopToWord.compHOL ctxt p labels).1) {word with clock := 6*limit} =
        (wordResult,{wordPost with clock := 6*limit-(word.clock-wordPost.clock)}) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      WordSteps.steps (compileExp (LoopToWord.compHOL ctxt p labels).1) {word with clock := 6*limit} ≤
        sizeOf (compileExp (LoopToWord.compHOL ctxt p labels).1) * (6*limit+1) := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram (loopSequenceSource_select shape))
      source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,_,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have bound : WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 word ≤ 6*limit := by omega
  have normalized := loopSequence_wordSimp_normalized (loopSequenceSource_word shape ctxt labels)
    word wordPost wordResult (6*limit) wordRun notTimeout bound gc
  exact ⟨wordPost,wordResult,normalized.1,wordFfi,wordRel,normalized.2⟩

end SteppedFlapjack.LoopToWordSteps
