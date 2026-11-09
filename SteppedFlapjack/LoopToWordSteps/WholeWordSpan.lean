import SteppedFlapjack.LoopToWordSteps.TailEntryWordSimp
import SteppedFlapjack.WordAllocSteps.WholeTailCode
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps
variable {C F : Type}
/-- A completed single-entry Loop run yields the corresponding result and FFI
events in the actual fully optimized Word code, within an explicit visit bound. -/
theorem singleTail_wholeWord_span {dest : Nat} {p callee : HolLoopProg 64}
    (shape : SingleTailEntryShape dest p) (calleeShape : LoopSequenceSource callee)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (start : Nat) (starter : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (limit : Nat) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wc : Config) (ac : AsmConfigExact 64)
    (entryMember : (start,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (calleeMember : (dest,1,loopToWordCompFuncHOL dest [] callee) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (shapes : TailProgramShapes programs)
    (code : starter.code = sptFromAList programs)
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (lookup : sptLookup dest source.code = some ([],callee))
    (premises : let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
      evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    let k := ac.regCount-(5+ac.avoidRegs.length)
    let entryOut := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
      ((start,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs start)).2.2
    let calleeOut := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
      ((dest,1,loopToWordCompFuncHOL dest [] callee),entryColour wc programs dest)).2.2
    let final := evaluate (.call none (some start) [0] none)
      {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2}
    ∃ wordPost wordResult,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0)
        (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter))
        result sourcePost wordResult wordPost ∧
      final.1 = wordResult ∧ final.2.ffi = sourcePost.ffi ∧
      WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2} ≤
        1 + wordControlWeight entryOut * (wordControlWeight calleeOut+1) * (6*limit+2) := by
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
  have found : findCode (some dest) [] source.code = some (.ln,callee) := by simp [findCode,lookup,sptFromAList]
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    singleTailEntry_correct_with_steps shape callee (loopSequence_program calleeShape) source found
      result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨wordComplete,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have codeRel := premises.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,codeRelation⟩ := codeRel
  have codeBound := singleTail_word_codeBound shape calleeShape source.code word.code codeRelation lookup ctxt labels
  have wordNoInstall : WordProps.noInstallCode word.code := by
    change WordProps.noInstallCode starter.code
    rw [code]
    exact (wholeCompile_tail_codeRelations wc ac programs shapes).1
  have entryShape := tailEntry_word (singleTail_to_tail shape) ctxt labels
  have normalized := tailEntry_normalized_run entryShape word wordPost wordResult _ (6*limit)
    (tailEntry_noInstall entryShape) wordNoInstall codeBound wordRun notError notTimeout
      (wordBound.trans (Nat.mul_le_mul_left 6 sourceBound))
  have entryLookup := (wholeCompile_entry_lookups wc ac programs start 1 _ entryMember nodup).1
  have arg0 : getVar 0 {starter with clock := 6*limit+1} = some (.loc 1 0) := arg
  have args : getVars [0] {starter with clock := 6*limit+1} = some [(.loc 1 0 : WordLocW 64)] := by
    simp [WordSemStateFiniteExact.getVars,arg0]
  have wordFind : wordSemFindCode (some start) [(.loc 1 0 : WordLocW 64)]
      starter.code starter.stackSize = some ([.loc 1 0],(LoopToWord.compHOL ctxt p labels).1,
        sptLookup start starter.stackSize) := by simp [wordSemFindCode,code,entryLookup]
  have goodResult : wordSemBadFunReturn wordResult = false := by cases wordComplete <;> rfl
  have unoptimizedRun : evaluate (.call none (some start) [0] none) {starter with clock := 6*limit+1} =
      (wordResult,{wordPost with clock := 6*limit-(word.clock-wordPost.clock)}) := by
    rw [WordSemStateFiniteExact.evaluate]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,wordFind]
    simp only [show 6*limit+1 ≠ 0 by omega,↓reduceDIte]
    have h : callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize)
        (decClock {starter with clock := 6*limit+1}) = {word with clock := 6*limit} := by
      simp [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
    rw [h,normalized]
    simp [goodResult]
  have nonerror : (evaluate (.call none (some start) [0] none) {starter with clock := 6*limit+1}).1 ≠ some .error := by
    rw [unoptimizedRun]; exact notError
  have targetShape : LoopSequence (loopToWordCompFuncHOL dest [] callee) := by
    unfold loopToWordCompFuncHOL
    exact loopSequenceSource_word calleeShape _ _
  have target := wholeCompile_start_result_and_bound wc ac programs shapes starter start dest (6*limit+1)
    (LoopToWord.compHOL ctxt p labels).1 (loopToWordCompFuncHOL dest [] callee)
    entryMember calleeMember nodup (singleTail_word_allowed shape ctxt labels) targetShape code
    (.loc 1 0) arg gc stack nonerror
  refine ⟨wordPost,wordResult,wordRel,?_,?_,?_⟩
  · simpa [unoptimizedRun] using target.1
  · simpa [unoptimizedRun,wordFfi] using target.2.1
  · simpa only [Nat.add_assoc,show 6*limit+1+1 = 6*limit+2 by omega] using target.2.2
end SteppedFlapjack.LoopToWordSteps
