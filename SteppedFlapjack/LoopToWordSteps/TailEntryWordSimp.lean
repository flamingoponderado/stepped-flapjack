import SteppedFlapjack.WordSimpSteps.TailTargets
import SteppedFlapjack.LoopToWordSteps.TailCall
import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound

/-! A source-bounded Loop tail entry through the actual WordSimp pass. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps
open Flapjack.Compiler.Backend.WordSimp

/-- The compiler code relation derives the Word callee bound for the actual
single-destination entry, then WordSimp executes within a Loop-visit bound. -/
theorem singleTail_wordSimp_bound {F C : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (noInstallCode : WordProps.noInstallCode word.code) (sourceBound : LoopSteps.steps p source ≤ limit) :
    ∃ wordPost wordResult,
      WordSemStateFiniteExact.evaluate (compileExp (LoopToWord.compHOL ctxt p labels).1) {word with clock := 6*limit} =
        (wordResult,{wordPost with clock := 6*limit-(word.clock-wordPost.clock)}) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      WordSteps.steps (compileExp (LoopToWord.compHOL ctxt p labels).1) {word with clock := 6*limit} ≤
        sizeOf (compileExp (LoopToWord.compHOL ctxt p labels).1) *
          (sizeOf (loopToWordCompFuncHOL loc [] callee)+1) * (6*limit+1) := by
  have found : findCode (some loc) [] source.code = some (.ln,callee) := by
    simp [findCode,lookup,sptFromAList]
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    singleTailEntry_correct_with_steps shape callee (loopSequence_program calleeShape) source found
      result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have codeRel := premises.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,code⟩ := codeRel
  have codeBound := singleTail_word_codeBound shape calleeShape source.code word.code code lookup ctxt labels
  have normalized := tailEntry_wordSimp_normalized_derived (tailEntry_word (singleTail_to_tail shape) ctxt labels)
    word wordPost wordResult _ (6*limit) noInstallCode codeBound wordRun notError notTimeout
    (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound)) gc
  exact ⟨wordPost,wordResult,normalized.1,wordFfi,wordRel,normalized.2⟩

end SteppedFlapjack.LoopToWordSteps
