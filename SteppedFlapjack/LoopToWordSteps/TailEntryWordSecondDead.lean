import SteppedFlapjack.LoopToWordSteps.TailEntryWordSimp
import SteppedFlapjack.WordDeadSteps.SecondTailEntry

/-! Loop tail-entry bounds through the actual second dead-code pass. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.WordDeadSteps Flapjack.Compiler.Backend.WordUnreach

/-- A supported single-destination Loop entry yields an actual Word compiler
prefix execution bounded by its Loop visits and compiled syntax. -/
theorem singleTail_wordSecondDead_bound {F C : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (ac : AsmConfigExact 64) (flag : Bool) (count : Nat) (shape : SingleTailEntryShape loc p)
    (calleeShape : LoopSequenceSource callee)
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
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1))
      (compileExp (LoopToWord.compHOL ctxt p labels).1) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    let sourceWord := (LoopToWord.compHOL ctxt p labels).1
    let q := fullSsaCcTrans count (instSelect ac (maxVarHOL (compileExp sourceWord)+1) (compileExp sourceWord))
    let out := removeDeadProg (removeUnreach (threeToTwoRegProg flag (copyProp (wordCommonSubexpElim (removeDeadProg q)))))
    let K := sizeOf (loopToWordCompFuncHOL loc [] callee)
    ∃ wordPost wordResult selectedLocals ssaPost deadLocals,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      wordStateEqRel {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} ssaPost ∧
      WordSemStateFiniteExact.evaluate out {word with locals := locals,clock := 6*limit} =
        (wordResult,{ssaPost with locals := deadLocals}) ∧
      WordTailEntryShape out ∧ TailEntryCodeBound out word.code K ∧
      WordSteps.steps out {word with locals := locals,clock := 6*limit} ≤ sizeOf out * (K+1) * (6*limit+1) := by
  have found : findCode (some loc) [] source.code = some (.ln,callee) := by simp [findCode,lookup,sptFromAList]
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    singleTailEntry_correct_with_steps shape callee (loopSequence_program calleeShape) source found
      result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have codeRel := premises.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,code⟩ := codeRel
  have codeBound := singleTail_word_codeBound shape calleeShape source.code word.code code lookup ctxt labels
  obtain ⟨selectedLocals,ssaPost,deadLocals,run,rel,_,outShape,outCode,bound⟩ :=
    compilerPrefix_tailEntry_secondDead_correct ac flag _ count (tailEntry_word (singleTail_to_tail shape) ctxt labels)
      word wordPost wordResult _ (6*limit) locals noInstallCode codeBound wordRun notError notTimeout
      (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound)) gc vars localRel domain
  exact ⟨wordPost,wordResult,selectedLocals,ssaPost,deadLocals,wordRel,wordFfi,rel,run,outShape,outCode,bound⟩

end SteppedFlapjack.LoopToWordSteps
