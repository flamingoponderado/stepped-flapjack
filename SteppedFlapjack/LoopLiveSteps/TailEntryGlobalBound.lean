import SteppedFlapjack.LoopLiveSteps.TailEntryCode

/-! Whole tail-entry bounds from code shape and clock consumption. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- The selected zero-argument code entry has a supported shape and bounded syntax. -/
def TailCodeBound (code : Spt (List Nat × HolLoopProg width)) (loc K : Nat) : Prop :=
  ∀ body, sptLookup loc code = some ([],body) → LoopSequenceSource body ∧ sizeOf body ≤ K

/-- A tail-entry visit bound based on consumed clock and the largest supported
zero-argument callee, including failure and timeout executions. -/
theorem tailEntry_consumption_bound {p : HolLoopProg width} {loc : Nat} (shape : SingleTailEntryShape loc p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width)) (K : Nat)
    (code : TailCodeBound s.code loc K) (run : evaluate p s = (result,post)) :
    steps p s ≤ (sizeOf p + K) * (s.clock-post.clock+1) := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_static_bound (branch_branched h) s
    nlinarith
  | call =>
    cases hlookup : sptLookup loc s.code with
    | none =>
      rw [steps.eq_def]
      simp only [show getVars [] s = some [] from rfl,findCode,hlookup]
      simp_wf
      nlinarith
    | some entry =>
      obtain ⟨params,body⟩ := entry
      cases params with
      | cons param params =>
        rw [steps.eq_def]
        simp only [show getVars [] s = some [] from rfl,findCode,hlookup]
        simp_wf
        nlinarith
      | nil =>
        have ⟨calleeShape,calleeSize⟩ := code body hlookup
        have lookup : findCode (some loc) [] s.code = some (.ln,body) := by simp [findCode,hlookup,sptFromAList]
        by_cases clock : s.clock = 0
        · rw [steps.eq_def]
          simp only [show getVars [] s = some [] from rfl,lookup,Option.isSome_none,Bool.false_or,
            clock,beq_self_eq_true,if_true]
          simp_wf
          nlinarith
        · have bound := directTail_consumption_bound loc [] [] .ln s post body calleeShape result (by rfl) lookup clock run
          have sz : 1 + sizeOf body ≤ sizeOf (.call none (some loc) [] none : HolLoopProg width) + K := by simp_wf; omega
          exact bound.trans (Nat.mul_le_mul_right _ sz)
  | @seq a b ha hb iha ihb =>
    have size : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : HolLoopProg width) := by simp_wf
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | none =>
      simp only at run ⊢
      have firstBound := tailEntry_none_static (singleTail_to_tail ha) s middle first
      have codeEq := tailEntry_none_code (singleTail_to_tail ha) s middle first
      have secondBound := ihb middle post result (by simpa only [codeEq] using code) run
      have firstClock := evaluate_clock a s none middle first
      have secondClock := evaluate_clock b middle result post run
      have budget : middle.clock-post.clock+1 ≤ s.clock-post.clock+1 := by omega
      have scaled := Nat.mul_le_mul_left (sizeOf b + K) budget
      nlinarith
    | some r =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      have firstBound := iha s middle (some r) code first
      nlinarith
  | @mark p hp ih =>
    rw [steps_mark]
    have inner : evaluate p s = (result,post) := by simpa only [evaluate] using run
    have bound := ih s post result code inner
    simp_wf
    nlinarith

/-- Clock consumed by a tail-entry execution is at most twice its actual
visits, when each reached zero-argument callee has the supported shape. -/
theorem tailEntry_clock_consumed {p : HolLoopProg width} {loc : Nat} (shape : SingleTailEntryShape loc p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width)) (K : Nat)
    (code : TailCodeBound s.code loc K) (run : evaluate p s = (result,post)) :
    s.clock-post.clock ≤ 2 * steps p s := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_clock_consumed (branch_branched h) s post result run
    omega
  | call =>
    cases hlookup : sptLookup loc s.code with
    | none =>
      rw [evaluate] at run
      simp [findCode,hlookup] at run
      obtain ⟨_,rfl⟩ := run
      simp
    | some entry =>
      obtain ⟨params,body⟩ := entry
      cases params with
      | cons param params =>
        rw [evaluate] at run
        simp [findCode,hlookup] at run
        obtain ⟨_,rfl⟩ := run
        simp
      | nil =>
        have ⟨calleeShape,_⟩ := code body hlookup
        have lookup : findCode (some loc) [] s.code = some (.ln,body) := by simp [findCode,hlookup,sptFromAList]
        by_cases clock : s.clock = 0
        · omega
        · exact directTail_clock_consumed loc [] [] .ln s post body calleeShape result (by rfl) lookup clock run
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have firstBound := tailEntry_none_consumed (singleTail_to_tail ha) s middle first
      have codeEq := tailEntry_none_code (singleTail_to_tail ha) s middle first
      have secondBound := ihb middle post result (by simpa only [codeEq] using code) run
      have secondClock := evaluate_clock b middle result post run
      omega
    | some r =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      have firstBound := iha s middle (some r) code first
      omega
  | @mark p hp ih =>
    rw [steps_mark]
    have inner : evaluate p s = (result,post) := by simpa only [evaluate] using run
    have bound := ih s post result code inner
    omega

/-- The actual Loop optimizer preserves a completed tail-entry execution and
its visits are bounded by unoptimized visits, entry syntax and callee syntax.
The bound is independent of unused clock. -/
theorem optimise_tailEntry_source_bound {p : HolLoopProg 64} {loc : Nat} (shape : SingleTailEntryShape loc p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64)) (K : Nat)
    (code : TailCodeBound s.code loc K) (run : evaluate p s = (result,post))
    (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    SingleTailEntryShape loc (optimiseHOL p) ∧
    steps (optimiseHOL p) s ≤ (sizeOf (optimiseHOL p) + K) * (2 * steps p s + 1) := by
  have optRun : evaluate (optimiseHOL p) s = (result,post) := by
    apply optimise_correct p s result post
    refine ⟨run,?_,?_,?_,?_⟩ <;> cases complete <;> simp_all
  have optShape := optimise_singleTail shape
  have optBound := tailEntry_consumption_bound optShape s post result K code optRun
  have consumed := tailEntry_clock_consumed shape s post result K code run
  exact ⟨optRun,optShape,optBound.trans (Nat.mul_le_mul_left _ (by omega))⟩

end SteppedFlapjack.LoopLiveSteps
