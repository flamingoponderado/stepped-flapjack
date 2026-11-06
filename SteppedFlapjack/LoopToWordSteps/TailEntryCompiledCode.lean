import SteppedFlapjack.LoopToWordSteps.TailEntryWordAllocated
import SteppedFlapjack.WordAllocSteps.CompiledCodeTail

/-! Loop entries through the actual compiled Word code table. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps

/-- A bounded Loop tail entry yields an execution of its fully compiled Word
body on the related compiled code table, with a derived local Stack callee
condition and a visit bound depending on the original Loop limit. -/
theorem singleTail_compiledCode_word_bound {F C : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (compiledCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (locals : Spt (WordLocW 64)) (limit : Nat)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (noInstall : WordProps.noInstallCode word.code) (codeRel : codeRel word.code compiledCode)
    (codeDomain : sptDomain word.code = sptDomain compiledCode)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    let sourceWord := (LoopToWord.compHOL ctxt p labels).1
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,sourceWord),col)).2.2
    let wordLimit := sizeOf sourceWord * (wordCodeSize compiledCode+1) * (6*limit+1)
    RegTailShape out ∧ SteppedFlapjack.WordToStackSteps.RegTailLocalCode out compiledCode ∧
      noInstallSubprogsHOL out = true ∧ flatExpConventions out = true ∧ postAllocConventionsHOL regCount out = true ∧
    ∃ wordPost wordResult perm selectedLocals targetPost,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      wordStateEqRel {wordPost with code := compiledCode,permute := perm,locals := selectedLocals,clock := wordLimit-(6*limit-(6*limit-(word.clock-wordPost.clock)))} targetPost ∧
      evaluate out {word with code := compiledCode,locals := locals,clock := wordLimit} = (wordResult,targetPost) ∧
      WordSteps.steps out {word with code := compiledCode,locals := locals,clock := wordLimit} ≤
        sizeOf out * (wordCodeSize compiledCode+1) * (wordLimit+1) := by
  have found : findCode (some loc) [] source.code = some (.ln,callee) := by simp [findCode,lookup,sptFromAList]
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    singleTailEntry_correct_with_steps shape callee (loopSequence_program calleeShape) source found
      result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have loopWordCode := premises.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,code⟩ := loopWordCode
  have codeBound := singleTail_word_codeBound shape calleeShape source.code word.code code lookup ctxt labels
  obtain ⟨outShape,localCode,outNoInstall,outFlat,outConvention,perm,selectedLocals,targetPost,targetRun,targetRel,bound⟩ :=
    fullCompileSingle_compiledCode_tailEntry_correct ac ac.twoRegArith count name alg regCount col
      (tailEntry_word (singleTail_to_tail shape) ctxt labels) word wordPost wordResult compiledCode _ (6*limit) locals
      codeBound noInstall codeRel codeDomain gc wordRun notError notTimeout
      (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound)) localRel domain
  exact ⟨outShape,localCode,outNoInstall,outFlat,outConvention,wordPost,wordResult,perm,selectedLocals,targetPost,
    wordRel,wordFfi,targetRel,targetRun,bound⟩

end SteppedFlapjack.LoopToWordSteps
