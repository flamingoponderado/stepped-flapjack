import SteppedFlapjack.WordAllocSteps.WholeTailCode
import SteppedFlapjack.LoopToWordSteps.WholeCallProgram
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps
variable {C F : Type}
/-- A complete Loop run with calls throughout its function table reaches the
actual optimized Word start call, with an explicit output-table visit bound. -/
theorem loopTable_wholeWord_span {p : HolLoopProg 64}
    (shape : SimpleLoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (table : LoopTableSupported source.code)
    (start : Nat) (starter : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (limit : Nat) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wc : Config) (ac : AsmConfigExact 64)
    (entryMember : (start,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (safety : WordProgramSafety programs)
    (code : starter.code = sptFromAList programs)
    (arg : getVar 0 starter = some (.loc 1 0)) (stack : starter.stack = [])
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun)
    (premises : let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
      evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    let final := evaluate (.call none (some start) [0] none)
      {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2}
    ∃ wordPost wordResult,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0)
        (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter))
        result sourcePost wordResult wordPost ∧
      final.1 = wordResult ∧ final.2.ffi = sourcePost.ffi ∧
      WordSteps.steps (.call none (some start) [0] none)
        {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac programs).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac programs).2)) * (6*limit+1) := by
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopTable_correct_with_steps p source shape table result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨wordComplete,notError,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have wordNoMt : WordProps.noMtCode word.code := by simpa [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,code] using safety.2.1
  have wordNoInstall : WordProps.noInstallCode word.code := by simpa [word,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,code] using safety.1
  have normalized := WordToStackSteps.tableWord_normalized_run _ word wordPost wordResult (6*limit)
    (loopComp_noMt p ctxt labels) (loopComp_noInstall p ctxt labels) wordNoMt wordNoInstall wordRun notTimeout
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
  have target := wholeCompile_start_agrees wc ac programs safety starter start (6*limit+1) code gc stack nonerror
  refine ⟨wordPost,wordResult,wordRel,?_,?_,?_⟩
  · simpa [unoptimizedRun] using target.1
  · simpa [unoptimizedRun,wordFfi] using target.2.1
  · have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    rw [compileWith_eq_compile _ allocator]
    exact target.2.2

end SteppedFlapjack.LoopToWordSteps
