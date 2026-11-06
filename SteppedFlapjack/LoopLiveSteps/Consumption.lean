import SteppedFlapjack.LoopLiveSteps.ClockBound
import SteppedFlapjack.LoopSteps.ClockConsumption
import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound

/-! Loop source-clock consumption and evaluator visits. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- A branch-bodied loop consumes at most two clock units per evaluator visit,
including entry and exit cuts. -/
theorem loop_consumed (live exits : NumSet) {body : HolLoopProg width} (shape : LoopBranch body)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate (.loop live body exits) s = (result,post)) :
    s.clock-post.clock ≤ 2 * steps (.loop live body exits) s := by
  induction hc : s.clock using Nat.strongRecOn generalizing s post result with
  | _ clock ih =>
    rcases cut : cutRes live (none,s) with ⟨cutResult,entry⟩
    have cutBound := cutRes_clock_consumed live none s
    rw [cut] at cutBound
    simp only at cutBound
    cases cutResult with
    | some r =>
      have execution := run
      rw [evaluate,cut] at execution
      simp only [Prod.mk.injEq] at execution
      obtain ⟨_,rfl⟩ := execution
      rw [steps_loop,cut]
      simp only at cutBound ⊢
      omega
    | none =>
      rcases bodyRun : evaluate body entry with ⟨bodyResult,middle⟩
      have entryClock := cutRes_none_clock cut
      have bodyClock := evaluate_clock body entry bodyResult middle bodyRun
      have bodyBound := branchedProgram_clock_consumed (branch_branched shape) entry middle bodyResult bodyRun
      have execution := run
      rw [evaluate,cut] at execution
      simp only at execution
      rw [fix_clock_evaluate,bodyRun] at execution
      rw [steps_loop,cut]
      simp only
      rw [bodyRun]
      by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
      · have recurRun : evaluate (.loop live body exits) middle = (result,post) := by
          rcases continuing with h | h <;> rw [h] at execution <;> exact execution
        have smaller : middle.clock < s.clock := by omega
        have recur := ih middle.clock (by simpa [hc] using smaller) middle post result recurRun rfl
        have finalClock := evaluate_clock (.loop live body exits) middle result post recurRun
        rcases continuing with h | h <;> rw [h] <;> simp only <;> omega
      · have hnone : bodyResult ≠ none := fun h => continuing (Or.inl h)
        have hcont : bodyResult ≠ some (.continue 0) := fun h => continuing (Or.inr h)
        cases bodyResult with
        | none => exact (hnone rfl).elim
        | some r =>
          cases r <;> try (simp only at execution ⊢; cases execution; simp_all; omega)
          case «break» label =>
            cases label with
            | zero =>
              simp only at execution ⊢
              have exitBound := cutRes_clock_consumed exits none middle
              rw [execution] at exitBound
              simp only at exitBound
              omega
            | succ n => simp only at execution ⊢; cases execution; simp_all; omega

/-- Clock used by a supported execution is at most twice its actual visits. -/
theorem sequence_consumed {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) : s.clock - post.clock ≤ 2 * steps p s := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_clock_consumed (branch_branched h) s post result run
    omega
  | @loop live exits body h => exact loop_consumed live exits h s post result run
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstBound := iha s middle out first
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have secondBound := ihb middle post result run
      have secondClock := evaluate_clock b middle result post run
      omega
    | some x =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega

/-- Supported executions visit at most a syntax factor per consumed clock unit,
plus one. Unlike an initial-clock bound this is stable under clock padding. -/
theorem sequence_consumption_bound {p : HolLoopProg width} (shape : LoopSequenceSource p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) :
    steps p s ≤ sizeOf p * (s.clock - post.clock + 1) := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_static_bound (branch_branched h) s
    nlinarith
  | @loop live exits body h =>
    have bound := loop_steps_by_clock_consumption live exits body (branch_branched h) s post result run
    have size : 1 + sizeOf body ≤ sizeOf (.loop live body exits : HolLoopProg width) := by simp_wf; omega
    exact bound.trans (Nat.mul_le_mul_right _ size)
  | @seq a b ha hb iha ihb =>
    have size : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : HolLoopProg width) := by simp_wf
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstBound := iha s middle out first
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have secondBound := ihb middle post result run
      have secondClock := evaluate_clock b middle result post run
      have budget1 : s.clock - middle.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have budget2 : middle.clock - post.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have scaled1 := Nat.mul_le_mul_left (sizeOf a) budget1
      have scaled2 := Nat.mul_le_mul_left (sizeOf b) budget2
      nlinarith
    | some x =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      nlinarith

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
