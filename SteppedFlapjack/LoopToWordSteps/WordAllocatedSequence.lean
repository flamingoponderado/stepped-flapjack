import SteppedFlapjack.LoopToWordSteps.WordOptimizedSequence
import SteppedFlapjack.WordAllocSteps.StackReady

/-! Loop source bounds through the complete Word compiler. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.WordAlloc
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

/-- A completed Loop execution bounds visits in the actual fully compiled Word
function. The syntax factor includes every optimization and register allocation. -/
theorem loopSequence_wordAllocated_bound {F C : Type}
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (locals : Spt (WordLocW 64)) (limit : Nat)
    (premises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (sourceBound : LoopSteps.steps p source ≤ limit) :
    let compiled := (fullCompileSingle ac.twoRegArith regCount alg ac
      ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
    LoopBlock compiled ∧ noInstallSubprogsHOL compiled = true ∧
    flatExpConventions compiled = true ∧ postAllocConventionsHOL regCount compiled = true ∧
    ∃ wordPost wordResult selectedLocals targetPost,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      wordPost.ffi = sourcePost.ffi ∧
      wordStateEqRel {wordPost with locals := selectedLocals,clock := 6*limit-(word.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate compiled {word with locals := locals,clock := 6*limit} = (wordResult,targetPost) ∧
      WordSteps.steps compiled {word with locals := locals,clock := 6*limit} ≤ sizeOf compiled * (6*limit+1) := by
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRel,wordBound⟩ :=
    loopProgram_correct_with_steps (loopSelect_loopProgram (loopSequenceSource_select shape))
      source result sourcePost word ctxt (.loc 1 0) labels premises
  obtain ⟨_,nonerror,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have bound : WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 word ≤ 6*limit := by omega
  have wordShape := loopSequenceSource_word shape ctxt labels
  obtain ⟨selectedLocals,targetPost,targetRun,rel,targetBound⟩ :=
    compilerPrefix_alloc_correct ac ac.twoRegArith count name alg regCount col wordShape
      word wordPost wordResult locals (6*limit) wordRun nonerror notTimeout bound gc localRel domain
  have ready := fullCompileSingle_stackReady ac ac.twoRegArith count name alg regCount col wordShape
  refine ⟨ready.1,ready.2.1,ready.2.2.1,ready.2.2.2,?_⟩
  rw [fullCompileSingle_eq_alloc ac ac.twoRegArith count name alg regCount col wordShape]
  exact ⟨wordPost,wordResult,selectedLocals,targetPost,wordRel,wordFfi,rel,targetRun,targetBound⟩

end SteppedFlapjack.LoopToWordSteps
