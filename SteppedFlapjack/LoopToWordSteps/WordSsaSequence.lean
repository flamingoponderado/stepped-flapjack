import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound
import SteppedFlapjack.WordSsaSteps.Composition

/-! Loop-to-Word followed by WordSimp, selection and full SSA. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSsaSteps

/-- A completed Loop sequence yields a semantically related execution of the
actual WordSimp, selection and full SSA prefix, with an SSA visit bound based
on Loop source visits. -/
theorem loopSequence_wordSsa_bound {F C : Type}
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
    ∃ wordPost wordResult selectedLocals targetPost,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      Flapjack.WordAlloc.wordStateEqRel
        {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate
        (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1))) {word with locals := locals,clock := 6*limit} = (wordResult,targetPost) ∧
      WordSteps.steps
        (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1))) {word with locals := locals,clock := 6*limit} ≤
        sizeOf (fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1)
          (compileExp (LoopToWord.compHOL ctxt p labels).1))) * (6*limit+1) := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,nonerror,notTimeout,bound⟩ :=
    loopSequence_word_execution p shape source sourcePost result word ctxt labels limit premises complete sourceBound
  obtain ⟨selectedLocals,targetPost,_,targetRun,rel,targetBound⟩ :=
    simpSelectSsa_correct_with_steps ac count (loopSequenceSource_word shape ctxt labels)
      word wordPost wordResult locals (6*limit) wordRun nonerror notTimeout bound gc vars localRel domain
  exact ⟨wordPost,wordResult,selectedLocals,targetPost,wordRel,wordFfi,rel,targetRun,targetBound⟩

end SteppedFlapjack.LoopToWordSteps
