import SteppedFlapjack.LoopToWordSteps.LoopSetup

/-! Quantitative Loop-to-Word simulation for source loops. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm

/-- The real compiled loop satisfies the sixfold bound, using the already
proved body simulation and well-founded induction on the source clock. -/
theorem sixBoundedLoop {width : Nat} [NeZero width] {C F : Type}
    (live liveOut : NumSet) (body : HolLoopProg width)
    (bodyCorrect : ∀ s : LoopSemStateFiniteExact width F, SixBoundPropertyAt C body s) :
    ∀ source : LoopSemStateFiniteExact width F, SixBoundPropertyAt C (.loop live body liveOut) source := by
  have core : ∀ n, ∀ source : LoopSemStateFiniteExact width F, source.clock = n →
      SixBoundPropertyAt C (.loop live body liveOut) source := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro source sourceClock result sourceFinal target ctxt retv labels premises
      obtain ⟨sourceRun,notError,state,locals,ret,dimension,notWord,acc⟩ := premises
      obtain ⟨finalTarget,targetResult,targetRun,ffi,resultRel⟩ :=
        compileCorrect (.loop live body liveOut) source result sourceFinal target ctxt retv labels
          ⟨sourceRun,notError,state,locals,ret,dimension,notWord,acc⟩
      refine ⟨finalTarget,targetResult,targetRun,ffi,resultRel,?_⟩
      rcases cutRun : cutRes live (none,source) with ⟨cutResult,sourceCut⟩
      cases cutResult with
      | some r =>
        have zero := loopCut_stopped_clockZero live liveOut body source sourceFinal sourceCut (some r) result
          cutRun (by simp) sourceRun notError
        obtain ⟨_,_,_,_,clocks,_,_,_,_,_,_,_⟩ := state
        have targetZero : target.clock = 0 := by omega
        have count := LoopSteps.steps_pos (.loop live body liveOut) source
        simp only [LoopToWord.compHOL]
        rw [tickLoopTick_zero _ _ _ target targetZero]
        omega
      | none =>
        obtain ⟨targetCut,targetCutRun,entryState,entryLocals,entryRet⟩ :=
          loopCut_related live source sourceCut target ctxt retv cutRun state locals ret
        rcases bodyRun : LoopSemStateFiniteExact.evaluate body sourceCut with ⟨bodyResult,sourcePost⟩
        have bodyNotError := loopBody_notError live liveOut body source sourceCut sourcePost sourceFinal
          bodyResult result cutRun bodyRun sourceRun notError
        have bodyAcc : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
          acc k (by simpa [accVarsHOL] using hk)
        obtain ⟨targetPost,bodyTargetResult,bodyTargetRun,bodyFfi,bodyRelation,bodySteps⟩ :=
          bodyCorrect sourceCut bodyResult sourcePost targetCut ctxt retv labels
            ⟨bodyRun,bodyNotError,entryState,entryLocals,entryRet,dimension,notWord,bodyAcc⟩
        have targetCut' : WordSemStateFiniteExact.cutState (mkNewCutsetHOL ctxt live,.ln)
            (WordSemStateFiniteExact.decClock target) = some targetCut := targetCutRun
        by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
        · have recursiveRun : LoopSemStateFiniteExact.evaluate (.loop live body liveOut) sourcePost = (result,sourceFinal) := by
            have h := sourceRun
            rw [LoopSemStateFiniteExact.evaluate,cutRun] at h
            simp only at h
            rw [LoopSemStateFiniteExact.fix_clock_evaluate,bodyRun] at h
            rcases continuing with eq | eq <;> rw [eq] at h <;> exact h
          have bodyClock := LoopSemStateFiniteExact.evaluate_clock body sourceCut bodyResult sourcePost bodyRun
          have cutClock := cutRes_none_clock cutRun
          have recursiveClock : sourcePost.clock < n := by omega
          have continueData : wordSemContLoop bodyTargetResult = true ∧
              loopToWordStateRelHOLExact sourcePost targetPost ∧
              localsRelHOL ctxt sourcePost.locals targetPost.locals ∧ sptLookup 0 targetPost.locals = some retv := by
            rcases continuing with eq | eq
            · subst bodyResult
              simp only [resultCase] at bodyRelation
              obtain ⟨st,rr,rv,lc,_,_⟩ := bodyRelation
              rw [rr]
              exact ⟨rfl,st,lc,rv⟩
            · subst bodyResult
              simp only [resultCase] at bodyRelation
              obtain ⟨st,rr,rv,lc,_,_⟩ := bodyRelation
              rw [rr]
              exact ⟨rfl,st,lc,rv⟩
          obtain ⟨_,_,_,_,_,recursiveSteps⟩ := ih sourcePost.clock recursiveClock sourcePost rfl
            result sourceFinal targetPost ctxt retv labels
              ⟨recursiveRun,notError,continueData.2.1,continueData.2.2.1,
                continueData.2.2.2,dimension,notWord,acc⟩
          have bound := loop_continue_sixfold live liveOut body source sourceCut sourcePost bodyResult
            (mkNewCutsetHOL ctxt live) (mkNewCutsetHOL ctxt liveOut) (LoopToWord.compHOL ctxt body labels).1
            target targetCut targetPost bodyTargetResult cutRun bodyRun continuing targetCut' bodyTargetRun
            continueData.1 bodySteps (by simpa only [LoopToWord.compHOL] using recursiveSteps)
          simpa only [LoopToWord.compHOL] using bound
        · have stops : bodyResult ≠ none ∧ bodyResult ≠ some (.continue 0) := by
            constructor
            · intro eq; exact continuing (Or.inl eq)
            · intro eq; exact continuing (Or.inr eq)
          have targetStops := resultCase_noncontinuing ctxt retv targetCut targetPost sourcePost bodyResult
            bodyTargetResult bodyRelation bodyNotError stops
          have bound := loop_exit_sixfold live liveOut body source sourceCut sourcePost bodyResult
            (mkNewCutsetHOL ctxt live) (mkNewCutsetHOL ctxt liveOut) (LoopToWord.compHOL ctxt body labels).1
            target targetCut targetPost bodyTargetResult cutRun bodyRun stops targetCut' bodyTargetRun
            (Or.inl targetStops) bodySteps
          simpa only [LoopToWord.compHOL] using bound
  intro source
  exact core source.clock source rfl

end SteppedFlapjack.LoopToWordSteps
