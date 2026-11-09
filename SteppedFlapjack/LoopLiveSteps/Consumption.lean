import SteppedFlapjack.LoopLiveSteps.ClockBound
import SteppedFlapjack.LoopSteps.ClockConsumption
import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound

/-! Loop source-clock consumption and evaluator visits. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- Supported executions consume at most twice their actual visits. -/
theorem sequence_consumed {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) : s.clock - post.clock ≤ 2 * steps p s :=
  SteppedFlapjack.CrepToLoopSteps.scalarLoop_consumed (sequence_scalarLoop shape) s post result run

/-- Visits depend on consumed clock, not spare input clock. -/
theorem sequence_consumption_bound {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) :
    steps p s ≤ sizeOf p * (s.clock - post.clock + 1) :=
  SteppedFlapjack.CrepToLoopSteps.scalarLoop_consumption_bound (sequence_scalarLoop shape) s post result run

/-- For a completed supported run, the actual optimizer's visits are bounded
by optimized syntax and source visits, independently of spare input clock. -/
theorem optimise_complete_source_steps {p : HolLoopProg 64} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    LoopSequenceSource (optimiseHOL p) ∧
    steps (optimiseHOL p) s ≤ sizeOf (optimiseHOL p) * (2 * steps p s + 1) := by
  obtain ⟨optRun,optShape,_⟩ := optimise_complete_with_steps shape s post result run complete
  have optBound := sequence_consumption_bound optShape s post result optRun
  have used := sequence_consumed shape s post result run
  exact ⟨optRun,optShape,optBound.trans (Nat.mul_le_mul_left _ (by omega))⟩

/-- The optimized Loop body and its actual WordSimp output execute within a
bound derived from visits in the unoptimized source execution. -/
theorem optimise_wordSimp_source_bound {F C : Type} (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat)
    (run : evaluate p source = (result,sourcePost)) (complete : CompleteLoopResult result)
    (stateRel : loopToWordStateRelHOLExact source word)
    (localsRel : LoopToWord.localsRelHOL ctxt source.locals word.locals)
    (ret : sptLookup 0 word.locals = some (.loc 1 0)) (dim : goodDimindex 64)
    (retLabel : ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true)
    (vars : ∀ k, sptMem k (accVarsHOL (optimiseHOL p) .ln) → sptMem k ctxt)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk word.gcFun)
    (sourceBound : steps p source ≤ limit) :
    ∃ wordPost wordResult,
      WordSemStateFiniteExact.evaluate
        (Flapjack.Compiler.Backend.WordSimp.compileExp (LoopToWord.compHOL ctxt (optimiseHOL p) labels).1)
        {word with clock := 6 * (sizeOf (optimiseHOL p) * (2 * limit + 1))} =
        (wordResult,{wordPost with clock := 6 * (sizeOf (optimiseHOL p) * (2 * limit + 1)) - (word.clock-wordPost.clock)}) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      WordSteps.steps
        (Flapjack.Compiler.Backend.WordSimp.compileExp (LoopToWord.compHOL ctxt (optimiseHOL p) labels).1)
        {word with clock := 6 * (sizeOf (optimiseHOL p) * (2 * limit + 1))} ≤
        sizeOf (Flapjack.Compiler.Backend.WordSimp.compileExp (LoopToWord.compHOL ctxt (optimiseHOL p) labels).1) *
          (6 * (sizeOf (optimiseHOL p) * (2 * limit + 1)) + 1) := by
  obtain ⟨optRun,optShape,optBound⟩ := optimise_complete_source_steps shape source sourcePost result run complete
  have nonerror : result ≠ some .error := by cases complete <;> simp
  have bound : steps (optimiseHOL p) source ≤ sizeOf (optimiseHOL p) * (2 * limit + 1) :=
    optBound.trans (Nat.mul_le_mul_left _ (by omega))
  exact loopSequence_wordSimp_bound (optimiseHOL p) optShape source sourcePost result word ctxt labels _
    ⟨optRun,nonerror,stateRel,localsRel,ret,dim,retLabel,vars⟩ complete gc bound

end SteppedFlapjack.LoopLiveSteps
