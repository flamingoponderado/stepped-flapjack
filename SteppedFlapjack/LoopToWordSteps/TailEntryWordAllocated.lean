import SteppedFlapjack.LoopToWordSteps.TailEntryWordSimp
import SteppedFlapjack.WordAllocSteps.TailEntry

/-! Loop tail-entry bounds through the actual complete Word compiler. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps

/-- A single-destination Loop entry yields a bounded execution of the actual
fully compiled Word function, ready for the call-sequence stack proof. -/
theorem singleTail_wordAllocated_bound {F C : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (locals : Spt (WordLocW 64)) (limit : Nat)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (noInstallCode : WordProps.noInstallCode word.code)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
    let K := sizeOf (loopToWordCompFuncHOL loc [] callee)
    SteppedFlapjack.WordToStackSteps.CallSequence out ∧ noInstallSubprogsHOL out = true ∧
      flatExpConventions out = true ∧ postAllocConventionsHOL regCount out = true ∧
    ∃ wordPost wordResult selectedLocals targetPost,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      wordStateEqRel {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate out {word with locals := locals,clock := 6*limit} = (wordResult,targetPost) ∧
      RegTailCodeBound out word.code K ∧
      WordSteps.steps out {word with locals := locals,clock := 6*limit} ≤ sizeOf out * (K+1) * (6*limit+1) := by
  have found : findCode (some loc) [] source.code = some (.ln,callee) := by simp [findCode,lookup,sptFromAList]
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    singleTailEntry_correct_with_steps shape callee (loopSequence_program calleeShape) source found
      result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have codeRel := premises.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,code⟩ := codeRel
  have codeBound := singleTail_word_codeBound shape calleeShape source.code word.code code lookup ctxt labels
  obtain ⟨callShape,noInstall,flat,postAlloc,selectedLocals,targetPost,run,rel,outCode,bound⟩ :=
    fullCompileSingle_tailEntry_correct ac ac.twoRegArith count name alg regCount col
      (tailEntry_word (singleTail_to_tail shape) ctxt labels) word wordPost wordResult _ (6*limit) locals
      noInstallCode codeBound wordRun notError notTimeout (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound))
      gc localRel domain
  exact ⟨callShape,noInstall,flat,postAlloc,wordPost,wordResult,selectedLocals,targetPost,
    wordRel,wordFfi,rel,run,outCode,bound⟩

end SteppedFlapjack.LoopToWordSteps
