import SteppedFlapjack.LoopLiveSteps.TailEntryCode

/-! Whole tail-entry bounds from code shape and clock consumption. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- The largest Loop control weight in the actual code table. -/
def loopCodeWeight {width : Nat} [NeZero width] (code : Spt (List Nat × HolLoopProg width)) : Nat :=
  (sptToAList code).foldr (fun row weight => max (SteppedFlapjack.CrepToLoopSteps.loopVisitWeight row.2.2) weight) 1

/-- Every reached code body is bounded by the computed table weight. -/
theorem loopCodeWeight_lookup {width : Nat} [NeZero width]
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (params : List Nat) (body : HolLoopProg width)
    (found : sptLookup loc code = some (params,body)) : SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body ≤ loopCodeWeight code := by
  have member : (loc,(params,body)) ∈ sptToAList code := (sptToAList_mem_iff_lookup code loc (params,body)).mpr found
  have aux (rows : List (Nat × (List Nat × HolLoopProg width))) : ∀ row ∈ rows,
      SteppedFlapjack.CrepToLoopSteps.loopVisitWeight row.2.2 ≤ rows.foldr (fun row weight => max (SteppedFlapjack.CrepToLoopSteps.loopVisitWeight row.2.2) weight) 1 := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      intro entry member
      simp only [List.mem_cons] at member
      cases member with
      | inl same => subst entry; simp
      | inr inRest => exact (ih entry inRest).trans (Nat.le_max_right _ _)
  exact aux _ _ member

/-- A successful direct code lookup is bounded by the actual table weight. -/
theorem findCode_direct_weight {width : Nat} [NeZero width]
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (found : findCode (some loc) values code = some (env,body)) :
    SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body ≤ loopCodeWeight code := by
  cases lookup : sptLookup loc code with
  | none => simp [findCode,lookup] at found
  | some pair =>
    obtain ⟨params,callee⟩ := pair
    by_cases arity : values.length = params.length
    · simp [findCode,lookup,arity] at found
      obtain ⟨_,rfl⟩ := found
      exact loopCodeWeight_lookup code loc params callee lookup
    · simp [findCode,lookup,arity] at found

/-- A reached direct tail call lifts its callee bound using the actual code-table weight. -/
theorem directTail_weighted_step {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args : List Nat) (s post : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (out : Option (LoopResultExact width)) (extra : Nat)
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (clock : s.clock ≠ 0)
    (run : evaluate body {decClock s with locals := env} = (out,post))
    (bodyBound : steps body {decClock s with locals := env} ≤
      SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body + (loopCodeWeight s.code+extra) * ((decClock s).clock-post.clock)) :
    steps (.call none (some loc) args none) s ≤ 1 + (loopCodeWeight s.code+extra) * (s.clock-post.clock) := by
  have weight := findCode_direct_weight s.code loc values env body found
  have count := steps_call_tail (some loc) args s values env body get found clock
  have bodyClock := evaluate_clock body {decClock s with locals := env} out post run
  simp only [decClock] at bodyClock bodyBound count
  have difference : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
  rw [count,difference]
  nlinarith

/-- A returning call cannot increase the clock after its callee finishes. -/
theorem returningCall_post_clock {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live : NumSet)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post)) :
    (evaluate (.call (some (names,live)) dest args handler) s).2.clock ≤ post.clock := by
  conv => lhs; rw [evaluate]
  simp only [get,found,distinct,not_true_eq_false,if_false]
  rw [cutRun]
  simp only
  rw [fix_clock_evaluate,bodyRun]
  cases out with
  | none => simp
  | some r =>
    cases r <;> try simp
    case result returned =>
      by_cases arity : returned.length = names.length
      · simp only [arity]
        cases handler with
        | none => simp [setVars]
        | some h =>
          obtain ⟨exception,handler,normal,liveOut⟩ := h
          simp only
          rcases run : evaluate normal (setVars names returned {post with locals := cut.locals}) with ⟨res,final⟩
          have h := evaluate_clock normal _ res final run
          simp only [if_true]
          have c := cutRes_clock_le liveOut (res,final)
          simp only [setVars] at h
          exact c.trans h
      · simp [arity]
    case exception value =>
      cases handler with
      | none => simp
      | some h =>
        obtain ⟨exception,handler,normal,liveOut⟩ := h
        simp only
        rcases run : evaluate handler (setVar exception value {post with locals := cut.locals}) with ⟨res,final⟩
        have h := evaluate_clock handler _ res final run
        have c := cutRes_clock_le liveOut (res,final)
        simp only [setVar] at h
        exact c.trans h


/-- A compiled returning call lifts its callee bound using the code-table weight. -/
private theorem returningCall_weighted_step_aux {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat) (handler normal : HolLoopProg width) (continuationCost : Nat)
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (handlerBound : ∀ t : LoopSemStateFiniteExact width F, steps handler t ≤ continuationCost)
    (normalBound : ∀ t : LoopSemStateFiniteExact width F, steps normal t ≤ continuationCost)
    (bodyBound : steps body {cut with locals := env} ≤ SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body +
      (loopCodeWeight s.code+continuationCost) * (cut.clock-post.clock)) :
    let call : HolLoopProg width := .call (some (names,live)) (some loc) args
      (some (exception,handler,normal,liveOut))
    steps call s ≤ 1 + (loopCodeWeight s.code+continuationCost) * (s.clock-(evaluate call s).2.clock) := by
  have weight := findCode_direct_weight s.code loc values env body found
  have count := steps_call_returning (some loc) args names live
    (some (exception,handler,normal,liveOut)) s cut post values env body out get found distinct cutRun bodyRun
  have countBound : steps (.call (some (names,live)) (some loc) args
      (some (exception,handler,normal,liveOut))) s ≤ 1 + continuationCost + steps body {cut with locals := env} := by
    rw [count]
    cases out with
    | none => simp
    | some r =>
      cases r <;> try simp
      case result returned =>
        by_cases arity : returned.length = names.length
        · simp [arity]
          have h := normalBound (setVars names returned {post with locals := cut.locals})
          omega
        · simp [arity]
      case exception value =>
        have h := handlerBound (setVar exception value {post with locals := cut.locals})
        omega
  have cutClock := cutRes_none_clock cutRun
  have bodyClock := evaluate_clock body {cut with locals := env} out post bodyRun
  simp only at bodyClock
  have finalClock := returningCall_post_clock (some loc) args names live
    (some (exception,handler,normal,liveOut)) s cut post values env body out get found distinct cutRun bodyRun
  have budget : cut.clock-post.clock + 1 ≤
      s.clock-(evaluate (.call (some (names,live)) (some loc) args
        (some (exception,handler,normal,liveOut))) s).2.clock := by omega
  have scaled := Nat.mul_le_mul_left (loopCodeWeight s.code+continuationCost) budget
  dsimp only
  nlinarith

/-- Compiler-generated returning continuations, including their optimizer marks,
are bounded by the code-table factor plus two visits. -/
theorem returningCall_weighted_step {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (markHandler markNormal : Bool)
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (bodyBound : steps body {cut with locals := env} ≤ SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body +
      (loopCodeWeight s.code+2) * (cut.clock-post.clock)) :
    let handler : HolLoopProg width := if markHandler then .mark (.raise exception) else .raise exception
    let normal : HolLoopProg width := if markNormal then .mark .skip else .skip
    let call : HolLoopProg width := .call (some (names,live)) (some loc) args (some (exception,handler,normal,liveOut))
    steps call s ≤ 1 + (loopCodeWeight s.code+2) * (s.clock-(evaluate call s).2.clock) := by
  apply returningCall_weighted_step_aux loc args names live liveOut exception _ _ 2 s cut post values env body out
    get found distinct cutRun bodyRun
  · intro t
    cases markHandler <;> simp [steps_mark,steps_leaf]
  · intro t
    cases markNormal <;> simp [steps_mark,steps_leaf]
  · exact bodyBound

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
      have codeEq := evaluate_code a s middle none first
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
      have codeEq := evaluate_code a s middle none first
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
