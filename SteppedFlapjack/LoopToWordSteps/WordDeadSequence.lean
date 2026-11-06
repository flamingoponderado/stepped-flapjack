import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound
import SteppedFlapjack.WordDeadSteps.Correct

/-! Loop-to-Word followed by WordSimp, selection and full SSA. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps SteppedFlapjack.WordDeadSteps Flapjack.WordAlloc

/-- A completed Loop sequence yields a semantically related execution of the
actual WordSimp, selection, full SSA and dead-code prefix, with a dead-code output visit bound based
on Loop source visits. -/
theorem loopSequence_wordDead_bound {F C : Type}
    (ac : AsmConfigExact 64) (count : Nat) (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (locals : Spt (WordLocW 64)) (limit : Nat)
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1))
      (compileExp (LoopToWord.compHOL ctxt p labels).1) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    ∃ wordPost wordResult selectedLocals targetPost deadLocals,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      Flapjack.WordAlloc.wordStateEqRel
        {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate
        (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1)))) {word with locals := locals,clock := 6*limit} = (wordResult,{targetPost with locals := deadLocals}) ∧
      WordSteps.steps
        (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1)))) {word with locals := locals,clock := 6*limit} ≤
        sizeOf (removeDeadProg (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1)))) * (6*limit+1) := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram (loopSequenceSource_select shape))
      source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,nonerror,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have bound : WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 word ≤ 6*limit := by omega
  obtain ⟨selectedLocals,targetPost,deadLocals,targetRun,rel,_,targetBound⟩ :=
    compilerPrefix_removeDead_correct ac count (loopSequenceSource_word shape ctxt labels)
      word wordPost wordResult locals (6*limit) wordRun nonerror notTimeout bound gc vars localRel domain
  exact ⟨wordPost,wordResult,selectedLocals,targetPost,deadLocals,wordRel,wordFfi,rel,targetRun,targetBound⟩

end SteppedFlapjack.LoopToWordSteps
