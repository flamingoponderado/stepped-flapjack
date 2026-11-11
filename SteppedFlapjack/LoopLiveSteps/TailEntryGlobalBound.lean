import SteppedFlapjack.LoopSteps.IterationShift
import SteppedFlapjack.LoopLiveSteps.TailEntryCode
import SteppedFlapjack.LoopLiveSteps.TailEntryBound
import SteppedFlapjack.LoopLiveSteps.ExecutableBranch

/-! Whole tail-entry bounds from code shape and clock consumption. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps SteppedFlapjack.CrepToLoopSteps
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

/-- A successful direct call identifies an actual code-table entry. -/
theorem findCode_direct_body {width : Nat} [NeZero width]
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (found : findCode (some loc) values code = some (env,body)) :
    ∃ params, sptLookup loc code = some (params,body) := by
  cases lookup : sptLookup loc code with
  | none => simp [findCode,lookup] at found
  | some pair =>
    obtain ⟨params,callee⟩ := pair
    by_cases arity : values.length = params.length
    · simp [findCode,lookup,arity] at found
      obtain ⟨_,rfl⟩ := found
      exact ⟨params,rfl⟩
    · simp [findCode,lookup,arity] at found

/-- A successful direct code lookup is bounded by the actual table weight. -/
theorem findCode_direct_weight {width : Nat} [NeZero width]
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (found : findCode (some loc) values code = some (env,body)) :
    SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body ≤ loopCodeWeight code := by
  obtain ⟨params,lookup⟩ := findCode_direct_body code loc values env body found
  exact loopCodeWeight_lookup code loc params body lookup

/-- A reached direct tail call lifts its callee bound using the actual code-table weight. -/
theorem directTail_weighted_step {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args : List Nat) (s post : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (out : Option (LoopResultExact width)) (K : Nat)
    (tableWeight : loopCodeWeight s.code ≤ K)
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (clock : s.clock ≠ 0)
    (run : evaluate body {decClock s with locals := env} = (out,post))
    (bodyBound : steps body {decClock s with locals := env} ≤
      SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body + K * ((decClock s).clock-post.clock)) :
    steps (.call none (some loc) args none) s ≤ 1 + K * (s.clock-post.clock) := by
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
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat) (handler normal : HolLoopProg width) (continuationCost K : Nat)
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (tableWeight : loopCodeWeight s.code+continuationCost ≤ K)
    (handlerBound : ∀ t : LoopSemStateFiniteExact width F, steps handler t ≤ continuationCost)
    (normalBound : ∀ t : LoopSemStateFiniteExact width F, steps normal t ≤ continuationCost)
    (bodyBound : steps body {cut with locals := env} ≤ SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body +
      K * (cut.clock-post.clock)) :
    let call : HolLoopProg width := .call (some (names,live)) (some loc) args
      (some (exception,handler,normal,liveOut))
    steps call s ≤ 1 + K * (s.clock-(evaluate call s).2.clock) := by
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
  have scaled := Nat.mul_le_mul_left K budget
  dsimp only
  nlinarith

/-- Compiler-generated returning continuations, including their optimizer marks,
are bounded by the code-table factor plus two visits. -/
theorem returningCall_weighted_step {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (markHandler markNormal : Bool) (K : Nat)
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (tableWeight : loopCodeWeight s.code+2 ≤ K)
    (bodyBound : steps body {cut with locals := env} ≤ SteppedFlapjack.CrepToLoopSteps.loopVisitWeight body +
      K * (cut.clock-post.clock)) :
    let handler : HolLoopProg width := if markHandler then .mark (.raise exception) else .raise exception
    let normal : HolLoopProg width := if markNormal then .mark .skip else .skip
    let call : HolLoopProg width := .call (some (names,live)) (some loc) args (some (exception,handler,normal,liveOut))
    steps call s ≤ 1 + K * (s.clock-(evaluate call s).2.clock) := by
  apply returningCall_weighted_step_aux loc args names live liveOut exception _ _ 2 K s cut post values env body out
    get found distinct cutRun bodyRun tableWeight
  · intro t
    cases markHandler <;> simp [steps_mark,steps_leaf]
  · intro t
    cases markNormal <;> simp [steps_mark,steps_leaf]
  · exact bodyBound

private theorem returningCall_post_consumed_aux {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (handler normal : HolLoopProg width) (s cut post : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (handlerClock : ∀ t : LoopSemStateFiniteExact width F, (evaluate handler t).2.clock = t.clock)
    (normalClock : ∀ t : LoopSemStateFiniteExact width F, (evaluate normal t).2.clock = t.clock) :
    post.clock - (evaluate (.call (some (names,live)) dest args (some (exception,handler,normal,liveOut))) s).2.clock ≤ 1 := by
  conv => lhs; rhs; rw [evaluate]
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
      · simp only [arity,if_true]
        let state := setVars names returned {post with locals := cut.locals}
        rcases run : evaluate normal state with ⟨res,final⟩
        have clockEq := normalClock state
        rw [run] at clockEq
        have c := LoopSteps.cutRes_clock_consumed liveOut res final
        simp only [state,setVars] at clockEq
        omega
      · simp [arity]
    case exception value =>
      let state := setVar exception value {post with locals := cut.locals}
      rcases run : evaluate handler state with ⟨res,final⟩
      have clockEq := handlerClock state
      rw [run] at clockEq
      have c := LoopSteps.cutRes_clock_consumed liveOut res final
      simp only [state,setVar] at clockEq
      omega

/-- A compiler-generated normal or exception continuation consumes at most one
additional clock unit after its callee, including optimizer marks. -/
theorem returningCall_post_consumed {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (markHandler markNormal : Bool) (s cut post : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post)) :
    let handler : HolLoopProg width := if markHandler then .mark (.raise exception) else .raise exception
    let normal : HolLoopProg width := if markNormal then .mark .skip else .skip
    post.clock - (evaluate (.call (some (names,live)) dest args (some (exception,handler,normal,liveOut))) s).2.clock ≤ 1 := by
  apply returningCall_post_consumed_aux dest args names live liveOut exception _ _ s cut post values env body out
    get found distinct cutRun bodyRun
  · intro t
    cases markHandler <;> simp [evaluate,LoopSemStateFiniteExact.callEnv]
    all_goals split <;> rfl
  · intro t
    cases markNormal <;> simp [evaluate]

/-- The returning-call clock bound follows from its callee induction bound. -/
theorem returningCall_consumed_step {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (markHandler markNormal : Bool) (s cut post : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (bodyBound : cut.clock-post.clock ≤ 2 * LoopSteps.steps body {cut with locals := env}) :
    let handler : HolLoopProg width := if markHandler then .mark (.raise exception) else .raise exception
    let normal : HolLoopProg width := if markNormal then .mark .skip else .skip
    let call : HolLoopProg width := .call (some (names,live)) dest args (some (exception,handler,normal,liveOut))
    s.clock - (evaluate call s).2.clock ≤ 2 * LoopSteps.steps call s := by
  let handler : HolLoopProg width := if markHandler then .mark (.raise exception) else .raise exception
  let normal : HolLoopProg width := if markNormal then .mark .skip else .skip
  let call : HolLoopProg width := .call (some (names,live)) dest args (some (exception,handler,normal,liveOut))
  have count := LoopSteps.steps_call_returning dest args names live (some (exception,handler,normal,liveOut))
    s cut post values env body out get found distinct cutRun bodyRun
  have lower : 1 + LoopSteps.steps body {cut with locals := env} ≤ LoopSteps.steps call s := by
    dsimp only [call]
    rw [count]
    omega
  have first := LoopSteps.cutRes_clock_consumed live none s
  rw [cutRun] at first
  have firstLe := cutRes_clock_le live (none,s)
  rw [cutRun] at firstLe
  have bodyLe := evaluate_clock body {cut with locals := env} out post bodyRun
  have last := returningCall_post_consumed dest args names live liveOut exception markHandler markNormal
    s cut post values env body out get found distinct cutRun bodyRun
  have lastLe := returningCall_post_clock dest args names live (some (exception,handler,normal,liveOut))
    s cut post values env body out get found distinct cutRun bodyRun
  simp only at first firstLe bodyLe last lastLe
  dsimp only [call,handler,normal] at lower ⊢
  dsimp only [handler,normal] at lastLe
  omega

/-- Every function body in the table has the call-aware Loop shape. -/
def LoopTableSupported (code : Spt (List Nat × HolLoopProg width)) : Prop :=
  ∀ loc params body, sptLookup loc code = some (params,body) → SimpleLoopSequenceSource body

private theorem terminal_weighted (x y z a k visits : Nat)
    (hxy : y < x) (hzy : z ≤ y) (bound : visits ≤ a + k * (y-z)) :
    1 + visits ≤ 1+a+k*(x-z) := by
  have budget : y-z ≤ x-z := by omega
  have scaled := Nat.mul_le_mul_left k budget
  nlinarith

private theorem loop_weighted_step (live exits : NumSet) (body : HolLoopProg width)
    (a k : Nat) (dominates : 1 + a ≤ k)
    (s final : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate (.loop live body exits) s = (result,final))
    (bodyBound : ∀ (t u : LoopSemStateFiniteExact width F) (r : Option (LoopResultExact width)),
      t.clock < s.clock → t.code = s.code → evaluate body t = (r,u) → steps body t ≤ a + k * (t.clock-u.clock))
    (recurBound : ∀ (t u : LoopSemStateFiniteExact width F) (r : Option (LoopResultExact width)),
      t.clock < s.clock → t.code = s.code → evaluate (.loop live body exits) t = (r,u) →
      steps (.loop live body exits) t ≤ (1+a) + k * (t.clock-u.clock)) :
    steps (.loop live body exits) s ≤ (1+a) + k * (s.clock-final.clock) := by
  rcases cut : cutRes live (none,s) with ⟨cutResult,entry⟩
  cases cutResult with
  | some r =>
    rw [steps_loop,cut]
    simp only
    omega
  | none =>
    rcases bodyRun : evaluate body entry with ⟨bodyResult,middle⟩
    have entryClock := cutRes_none_clock cut
    have bodyClock := evaluate_clock body entry bodyResult middle bodyRun
    have entryCode : entry.code = s.code := by
      have h := cutRes_code live none s
      rw [cut] at h
      exact h
    have middleCode := evaluate_code body entry middle bodyResult bodyRun
    have bodyVisits := bodyBound entry middle bodyResult entryClock entryCode bodyRun
    have execution := run
    rw [evaluate,cut] at execution
    simp only at execution
    rw [fix_clock_evaluate,bodyRun] at execution
    rw [steps_loop,cut]
    simp only
    rw [bodyRun]
    by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
    · have recurRun : evaluate (.loop live body exits) middle = (result,final) := by
        rcases continuing with h | h <;> rw [h] at execution <;> exact execution
      have smaller : middle.clock < s.clock := by omega
      have recur := recurBound middle final result smaller (middleCode.trans entryCode) recurRun
      have finalClock := evaluate_clock (.loop live body exits) middle result final recurRun
      have budget : entry.clock - middle.clock + (middle.clock - final.clock) + 1 ≤ s.clock - final.clock := by omega
      have scaled := Nat.mul_le_mul_left k budget
      rcases continuing with h | h <;> rw [h] <;> simp only <;> nlinarith
    · have hnone : bodyResult ≠ none := fun h => continuing (Or.inl h)
      have hcont : bodyResult ≠ some (.continue 0) := fun h => continuing (Or.inr h)
      cases bodyResult with
      | none => exact (hnone rfl).elim
      | some r =>
        cases r <;> try (simp only at execution ⊢; cases execution; exact terminal_weighted _ _ _ _ _ _ entryClock bodyClock bodyVisits)
        case «continue» label =>
          cases label with
          | zero => exact (hcont rfl).elim
          | succ n =>
            simp only at execution ⊢
            cases execution
            have budget : entry.clock - final.clock ≤ s.clock - final.clock := by omega
            have scaled := Nat.mul_le_mul_left k budget
            nlinarith
        case «break» label =>
          cases label with
          | zero =>
            simp only at execution ⊢
            have exitClock := cutRes_clock_le exits (none,middle)
            rw [execution] at exitClock
            simp only at exitClock
            have budget : entry.clock - middle.clock ≤ s.clock - final.clock := by omega
            have scaled := Nat.mul_le_mul_left k budget
            nlinarith
          | succ n =>
            simp only at execution ⊢
            cases execution
            have budget : entry.clock - final.clock ≤ s.clock - final.clock := by omega
            have scaled := Nat.mul_le_mul_left k budget
            nlinarith

set_option maxHeartbeats 5000000 in
/-- A call-aware Loop execution is bounded by its control weight and actual
clock consumption, using a factor computed from the complete code table. -/
theorem simpleSequence_global_bound (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) (K : Nat)
    (shape : SimpleLoopSequenceSource p) (code : LoopTableSupported s.code)
    (tableWeight : loopCodeWeight s.code + 2 ≤ K) (weight : loopVisitWeight p ≤ K) :
    steps p s ≤ loopVisitWeight p + (K) * (s.clock-(evaluate p s).2.clock) := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock,sizeOf p) = x → SimpleLoopSequenceSource p → LoopTableSupported s.code →
      loopCodeWeight s.code+2 ≤ K → loopVisitWeight p ≤ K →
      steps p s ≤ loopVisitWeight p + (K) * (s.clock-(evaluate p s).2.clock) := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx shape code tableWeight weight
      have ih : ∀ (q : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          SimpleLoopSequenceSource q → t.code = s.code → loopVisitWeight q ≤ K →
          steps q t ≤ loopVisitWeight q + (K) * (t.clock-(evaluate q t).2.clock) := by
        intro q t smaller hshape hcode hweight
        have supported : LoopTableSupported t.code := by rw [hcode]; exact code
        have bound := ih0 _ (hx ▸ smaller) q t rfl hshape supported (by simpa only [hcode] using tableWeight) hweight
        simpa only [hcode] using bound
      clear ih0 hx
      cases shape with
      | branch h =>
        have bound := branchedProgram_structural_bound (branch_branched h) s
        rw [branch_visitWeight h]
        omega
      | @loop live exits body h =>
        rcases run : evaluate (.loop live body exits) s with ⟨out,post⟩
        have w : 1 + loopVisitWeight body ≤ K := by
          simpa only [loopVisitWeight] using weight
        have bound := loop_weighted_step live exits body (loopVisitWeight body) (K)
          w s post out run (by
            intro t u r smaller same bodyRun
            have bodyWeight : loopVisitWeight body ≤ K := by omega
            have hbody := ih body t (lexLtClock smaller) h same bodyWeight
            rw [bodyRun] at hbody
            exact hbody) (by
            intro t u r smaller same loopRun
            have hloop := ih (.loop live body exits) t (lexLtClock smaller) (.loop live exits h) same weight
            rw [loopRun] at hloop
            simpa only [loopVisitWeight] using hloop)
        simpa only [run,loopVisitWeight] using bound
      | tail loc args =>
        cases hg : getVars args s with
        | none =>
          rw [steps.eq_def]
          simp [hg,loopVisitWeight]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none =>
            rw [steps.eq_def]
            simp [hg,hf,loopVisitWeight]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases clock : s.clock = 0
            · rw [steps.eq_def]
              simp [hg,hf,clock,loopVisitWeight]
            · obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
              have bodyShape := code loc params body lookup
              have bodyWeight := loopCodeWeight_lookup s.code loc params body lookup
              rcases bodyRun : evaluate body {decClock s with locals := env} with ⟨out,post⟩
              have smaller : (decClock s).clock < s.clock := by simp [decClock]; omega
              have bodyBound := ih body {decClock s with locals := env} (lexLtClock smaller) bodyShape rfl (by omega)
              rw [bodyRun] at bodyBound
              have bound := directTail_weighted_step loc args s post vals env body out K (by omega) hg hf clock bodyRun bodyBound
              have after : (evaluate (.call none (some loc) args none) s).2.clock = post.clock := by
                rw [evaluate]
                simp only [hg,hf,Option.isSome_none,Bool.false_eq_true,if_false,clock,dite_false,bodyRun]
                cases out with
                | none => rfl
                | some r => cases r <;> rfl
              rw [after]
              simpa [loopVisitWeight] using bound

      | returning names callLive loc exception args liveOut =>
        cases hg : getVars args s with
        | none =>
          rw [steps.eq_def]
          simp [hg,loopVisitWeight]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none =>
            rw [steps.eq_def]
            simp [hg,hf,loopVisitWeight]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases distinct : names.Nodup
            · rcases hcut : cutRes callLive (none,s) with ⟨cutResult,cut⟩
              cases cutResult with
              | some r =>
                rw [steps.eq_def]
                simp [hg,hf,distinct,hcut,loopVisitWeight]
              | none =>
                obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
                have bodyShape := code loc params body lookup
                have bodyWeight := loopCodeWeight_lookup s.code loc params body lookup
                rcases bodyRun : evaluate body {cut with locals := env} with ⟨out,post⟩
                have cutCode : cut.code = s.code := by have h := cutRes_code callLive none s; rw [hcut] at h; exact h
                have smaller := cutRes_none_clock hcut
                have bodyBound := ih body {cut with locals := env} (lexLtClock smaller) bodyShape cutCode (by omega)
                rw [bodyRun] at bodyBound
                have bound := returningCall_weighted_step loc args names callLive liveOut exception false false K s cut post vals env body out
                  hg hf distinct hcut bodyRun tableWeight bodyBound
                simpa [loopVisitWeight] using bound
            · rw [steps.eq_def]
              simp [hg,hf,distinct,loopVisitWeight]

      | returningMarked names callLive loc exception args liveOut =>
        cases hg : getVars args s with
        | none =>
          rw [steps.eq_def]
          simp [hg,loopVisitWeight]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none =>
            rw [steps.eq_def]
            simp [hg,hf,loopVisitWeight]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases distinct : names.Nodup
            · rcases hcut : cutRes callLive (none,s) with ⟨cutResult,cut⟩
              cases cutResult with
              | some r =>
                rw [steps.eq_def]
                simp [hg,hf,distinct,hcut,loopVisitWeight]
              | none =>
                obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
                have bodyShape := code loc params body lookup
                have bodyWeight := loopCodeWeight_lookup s.code loc params body lookup
                rcases bodyRun : evaluate body {cut with locals := env} with ⟨out,post⟩
                have cutCode : cut.code = s.code := by have h := cutRes_code callLive none s; rw [hcut] at h; exact h
                have smaller := cutRes_none_clock hcut
                have bodyBound := ih body {cut with locals := env} (lexLtClock smaller) bodyShape cutCode (by omega)
                rw [bodyRun] at bodyBound
                have bound := returningCall_weighted_step loc args names callLive liveOut exception true true K s cut post vals env body out
                  hg hf distinct hcut bodyRun tableWeight bodyBound
                simpa [loopVisitWeight] using bound
            · rw [steps.eq_def]
              simp [hg,hf,distinct,loopVisitWeight]

      | @conditional cmp reg ri live a b ha hb =>
        have wa : loopVisitWeight a ≤ K := by simp only [loopVisitWeight] at weight; omega
        have wb : loopVisitWeight b ≤ K := by simp only [loopVisitWeight] at weight; omega
        have ba := ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl wa
        have bb := ih b s (lexLt (Nat.le_refl _) (by simp_wf; omega)) hb rfl wb
        rw [steps_ite,evaluate]
        rcases hx : sptLookup reg s.locals with _ | (x | ⟨_,_⟩) <;>
          rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only <;>
          try (simp [loopVisitWeight]; omega)
        by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
        · simp only [hc,if_true]
          rcases arun : evaluate a s with ⟨r,t⟩
          rw [arun] at ba
          have cut := cutRes_clock_le live (r,t)
          have clk := evaluate_clock a s r t arun
          simp only at ba cut
          have delta : s.clock-t.clock ≤ s.clock-(cutRes live (r,t)).2.clock := by omega
          have scaled := Nat.mul_le_mul_left (K) delta
          simp only [loopVisitWeight]
          nlinarith
        · simp only [hc,Bool.false_eq_true,if_false]
          rcases brun : evaluate b s with ⟨r,t⟩
          rw [brun] at bb
          have cut := cutRes_clock_le live (r,t)
          have clk := evaluate_clock b s r t brun
          simp only at bb cut
          have delta : s.clock-t.clock ≤ s.clock-(cutRes live (r,t)).2.clock := by omega
          have scaled := Nat.mul_le_mul_left (K) delta
          simp only [loopVisitWeight]
          nlinarith

      | @seq a b ha hb =>
        have wa : loopVisitWeight a ≤ K := by simp only [loopVisitWeight] at weight; omega
        have wb : loopVisitWeight b ≤ K := by simp only [loopVisitWeight] at weight; omega
        have firstBound := ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl wa
        rw [steps_seq,evaluate_seq]
        rcases first : evaluate a s with ⟨out,middle⟩
        rw [first] at firstBound
        have firstClock := evaluate_clock a s out middle first
        cases out with
        | none =>
          simp only
          have codeEq := evaluate_code a s middle none first
          have secondBound := ih b middle (lexLt firstClock (by simp_wf)) hb codeEq wb
          rcases second : evaluate b middle with ⟨result,post⟩
          rw [second] at secondBound
          have secondClock := evaluate_clock b middle result post second
          have delta : s.clock-middle.clock + (middle.clock-post.clock) = s.clock-post.clock := by omega
          simp only [loopVisitWeight]
          nlinarith
        | some result =>
          simp only [loopVisitWeight]
          nlinarith

      | @mark q h =>
        have wq : loopVisitWeight q ≤ K := by simp only [loopVisitWeight] at weight; omega
        have bound := ih q s (lexLt (Nat.le_refl _) (by simp_wf)) h rfl wq
        simp only [steps_mark,evaluate,loopVisitWeight]
        omega
  exact key _ p s rfl shape code tableWeight weight

set_option maxHeartbeats 5000000 in
/-- Supported executions consume at most two clock units per visit, including nested calls. -/
theorem simpleSequence_global_consumed (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (shape : SimpleLoopSequenceSource p) (code : LoopTableSupported s.code) :
    s.clock-(evaluate p s).2.clock ≤ 2 * steps p s := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock,sizeOf p) = x → SimpleLoopSequenceSource p → LoopTableSupported s.code →
      s.clock-(evaluate p s).2.clock ≤ 2 * steps p s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx shape code
      have ih : ∀ (q : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          SimpleLoopSequenceSource q → t.code = s.code →
          t.clock-(evaluate q t).2.clock ≤ 2 * steps q t := by
        intro q t smaller hshape hcode
        have supported : LoopTableSupported t.code := by rw [hcode]; exact code
        exact ih0 _ (hx ▸ smaller) q t rfl hshape supported
      clear ih0 hx
      cases shape with
      | branch h =>
        rcases run : evaluate _ s with ⟨result,post⟩
        have bound := branchedProgram_clock_consumed (branch_branched h) s post result run
        simp only
        omega
      | @loop live exits body h =>
        rcases cut : cutRes live (none,s) with ⟨cutResult,entry⟩
        have cutBound := cutRes_clock_consumed live none s
        rw [cut] at cutBound
        simp only at cutBound
        cases cutResult with
        | some r =>
          have execution : evaluate (.loop live body exits) s = (some r,entry) := by
            rw [evaluate,cut]
          rw [execution,steps_loop,cut]
          simp only
          omega
        | none =>
          rcases bodyRun : evaluate body entry with ⟨bodyResult,middle⟩
          have entryClock := cutRes_none_clock cut
          have bodyClock := evaluate_clock body entry bodyResult middle bodyRun
          have entryCode : entry.code = s.code := by
            have hc := cutRes_code live none s
            rw [cut] at hc
            exact hc
          have middleCode := evaluate_code body entry middle bodyResult bodyRun
          have bodyBound := ih body entry (lexLtClock entryClock) h entryCode
          rw [bodyRun] at bodyBound
          simp only at bodyBound
          rcases run : evaluate (.loop live body exits) s with ⟨result,post⟩
          have execution := run
          rw [evaluate,cut] at execution
          simp only at execution
          rw [fix_clock_evaluate,bodyRun] at execution
          rw [steps_loop,cut]
          simp only
          rw [bodyRun]
          by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
          · have recurRun : evaluate (.loop live body exits) middle = (result,post) := by
              rcases continuing with hc | hc <;> rw [hc] at execution <;> exact execution
            have smaller : middle.clock < s.clock := by omega
            have recur := ih (.loop live body exits) middle (lexLtClock smaller)
              (.loop live exits h) (middleCode.trans entryCode)
            rw [recurRun] at recur
            simp only at recur
            have finalClock := evaluate_clock (.loop live body exits) middle result post recurRun
            rcases continuing with hc | hc <;> rw [hc] <;> simp only <;> omega
          · have hnone : bodyResult ≠ none := fun hc => continuing (Or.inl hc)
            have hcont : bodyResult ≠ some (.continue 0) := fun hc => continuing (Or.inr hc)
            cases bodyResult with
            | none => exact (hnone rfl).elim
            | some r =>
              cases r <;> try (simp only at execution ⊢; cases execution; omega)
              case «break» label =>
                cases label with
                | zero =>
                  simp only at execution ⊢
                  have exitBound := cutRes_clock_consumed exits none middle
                  rw [execution] at exitBound
                  simp only at exitBound
                  omega
                | succ n => simp only at execution ⊢; cases execution; omega
      | tail loc args =>
        cases hg : getVars args s with
        | none => simp [evaluate,hg]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none => simp [evaluate,hg,hf]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases clock : s.clock = 0
            · simp [clock]
            · obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
              have bodyShape := code loc params body lookup
              rcases bodyRun : evaluate body {decClock s with locals := env} with ⟨out,post⟩
              have smaller : (decClock s).clock < s.clock := by simp [decClock]; omega
              have bodyBound := ih body {decClock s with locals := env} (lexLtClock smaller) bodyShape rfl
              rw [bodyRun] at bodyBound
              have bound := tail_clock_consumed_from_body (some loc) args s post vals env body out hg hf clock bodyRun bodyBound
              have after : (evaluate (.call none (some loc) args none) s).2.clock = post.clock := by
                rw [evaluate]
                simp only [hg,hf,Option.isSome_none,Bool.false_eq_true,if_false,clock,dite_false,bodyRun]
                cases out with
                | none => rfl
                | some r => cases r <;> rfl
              rw [after]
              exact bound
      | returning names callLive loc exception args liveOut =>
        cases hg : getVars args s with
        | none => simp [evaluate,hg]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none => simp [evaluate,hg,hf]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases distinct : names.Nodup
            · rcases hcut : cutRes callLive (none,s) with ⟨cutResult,cut⟩
              cases cutResult with
              | some r =>
                have hc := cutRes_clock_consumed callLive none s
                rw [hcut] at hc
                have hp := steps_pos (.call (some (names,callLive)) (some loc) args (some (exception, .raise exception, .skip, liveOut))) s
                simp [evaluate,hg,hf,distinct,hcut]
                simp only at hc
                omega
              | none =>
                obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
                have bodyShape := code loc params body lookup
                rcases bodyRun : evaluate body {cut with locals := env} with ⟨out,post⟩
                have cutCode : cut.code = s.code := by have h := cutRes_code callLive none s; rw [hcut] at h; exact h
                have smaller := cutRes_none_clock hcut
                have bodyBound := ih body {cut with locals := env} (lexLtClock smaller) bodyShape cutCode
                rw [bodyRun] at bodyBound
                exact returningCall_consumed_step (some loc) args names callLive liveOut exception false false s cut post vals env body out hg hf distinct hcut bodyRun bodyBound
            · simp [evaluate,hg,hf,distinct]
      | returningMarked names callLive loc exception args liveOut =>
        cases hg : getVars args s with
        | none => simp [evaluate,hg]
        | some vals =>
          cases hf : findCode (some loc) vals s.code with
          | none => simp [evaluate,hg,hf]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            by_cases distinct : names.Nodup
            · rcases hcut : cutRes callLive (none,s) with ⟨cutResult,cut⟩
              cases cutResult with
              | some r =>
                have hc := cutRes_clock_consumed callLive none s
                rw [hcut] at hc
                have hp := steps_pos (.call (some (names,callLive)) (some loc) args (some (exception, .mark (.raise exception), .mark .skip, liveOut))) s
                simp [evaluate,hg,hf,distinct,hcut]
                simp only at hc
                omega
              | none =>
                obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body hf
                have bodyShape := code loc params body lookup
                rcases bodyRun : evaluate body {cut with locals := env} with ⟨out,post⟩
                have cutCode : cut.code = s.code := by have h := cutRes_code callLive none s; rw [hcut] at h; exact h
                have smaller := cutRes_none_clock hcut
                have bodyBound := ih body {cut with locals := env} (lexLtClock smaller) bodyShape cutCode
                rw [bodyRun] at bodyBound
                exact returningCall_consumed_step (some loc) args names callLive liveOut exception true true s cut post vals env body out hg hf distinct hcut bodyRun bodyBound
            · simp [evaluate,hg,hf,distinct]
      | @conditional cmp reg ri live a b ha hb =>
        have ba := ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl
        have bb := ih b s (lexLt (Nat.le_refl _) (by simp_wf; omega)) hb rfl
        rw [steps_ite,evaluate]
        rcases hx : sptLookup reg s.locals with _ | (x | ⟨_,_⟩) <;>
          rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only <;>
          try (simp; done)
        by_cases hc : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
        · simp only [hc,if_true]
          rcases arun : evaluate a s with ⟨r,t⟩
          rw [arun] at ba
          have cut := cutRes_clock_consumed live r t
          have clk := evaluate_clock a s r t arun
          simp only at ba cut
          omega
        · simp only [hc,Bool.false_eq_true,if_false]
          rcases brun : evaluate b s with ⟨r,t⟩
          rw [brun] at bb
          have cut := cutRes_clock_consumed live r t
          have clk := evaluate_clock b s r t brun
          simp only at bb cut
          omega

      | @seq a b ha hb =>
        have firstBound := ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl
        rw [steps_seq,evaluate_seq]
        rcases first : evaluate a s with ⟨out,middle⟩
        rw [first] at firstBound
        have firstClock := evaluate_clock a s out middle first
        cases out with
        | none =>
          simp only
          have codeEq := evaluate_code a s middle none first
          have secondBound := ih b middle (lexLt firstClock (by simp_wf)) hb codeEq
          rcases second : evaluate b middle with ⟨result,post⟩
          rw [second] at secondBound
          have secondClock := evaluate_clock b middle result post second
          simp only at firstBound secondBound ⊢
          omega
        | some result => simp only at firstBound ⊢; omega
      | @mark q h =>
        have bound := ih q s (lexLt (Nat.le_refl _) (by simp_wf)) h rfl
        simp only [steps_mark,evaluate]
        omega
  exact key _ p s rfl shape code

/-- A completed supported execution bounds the optimized execution using the
unoptimized visit count and the weight of the actual function table. -/
theorem optimise_simpleSequence_source_bound {p : HolLoopProg 64}
    (shape : SimpleLoopSequenceSource p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (code : LoopTableSupported s.code)
    (weight : loopVisitWeight (optimiseHOL p) ≤ loopCodeWeight s.code + 2)
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    steps (optimiseHOL p) s ≤ loopVisitWeight (optimiseHOL p) +
      (loopCodeWeight s.code + 2) * (2 * steps p s) := by
  have optRun : evaluate (optimiseHOL p) s = (result,post) := by
    apply optimise_correct p s result post
    refine ⟨run,?_,?_,?_,?_⟩ <;> cases complete <;> simp_all
  have optBound := simpleSequence_global_bound (optimiseHOL p) s (loopCodeWeight s.code+2) (optimise_simpleSequence shape) code (by rfl) weight
  have consumed := simpleSequence_global_consumed p s shape code
  rw [optRun] at optBound
  rw [run] at consumed
  exact ⟨optRun, optBound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ consumed) _)⟩

/-- A compiled callee bound lifts through the actual optimizer. -/
theorem optimise_callee_crep_bound {F : Type}
    (p : HolLoopProg 64) (shape : SimpleLoopSequenceSource p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (sourceProgram : CrepProgHOL 64) (source : CrepSemHOLState 64 F) (B loc : Nat) (params : List Nat)
    (table : LoopTableSupported s.code)
    (found : sptLookup loc s.code = some (params,optimiseHOL p))
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result)
    (bodyBound : steps p s ≤ B * CrepSteps.steps sourceProgram source) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    steps (optimiseHOL p) s ≤ (loopCodeWeight s.code+2) * (2*B+1) * CrepSteps.steps sourceProgram source := by
  have weight := loopCodeWeight_lookup s.code loc params (optimiseHOL p) found
  have bound := optimise_simpleSequence_source_bound shape s post result table (by omega) run complete
  have positive := CrepSteps.steps_pos sourceProgram source
  refine ⟨bound.1,?_⟩
  have w := Nat.le_add_right_of_le weight (k := 2)
  have scale : (loopCodeWeight s.code+2) * (2 * steps p s) ≤
      (loopCodeWeight s.code+2) * (2 * B * CrepSteps.steps sourceProgram source) :=
    Nat.mul_le_mul_left _ (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 bodyBound)
  nlinarith

/-- The unoptimized callee induction bounds its actual compiled tail call. -/
theorem compiledTailCall_optimised_bound_from_body {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL 64)) (shape : ∀ e ∈ args, DirectExpression e)
    (source : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (values : List (HolWordLab 64)) (params : List Nat) (body : CrepProgHOL 64) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : LoopTableSupported target.code)
    (bodyShape : SimpleLoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body))
    (bodyComplete : source.clock ≠ 0 → CompleteLoopResult
      (evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
        {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}).1)
    (bodyBound : source.clock ≠ 0 → LoopSteps.steps
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) target ≤
      max (2 * args.length + 3) ((loopCodeWeight target.code+2)*(2*B+1)) * CrepSteps.steps (.call none name args) source := by
  apply compiledTailCall_bound_from_body ctxt live name args shape source target values params body
    ((loopCodeWeight target.code+2)*(2*B+1)) hargs found arity distinct stateRel memRel globalsRel codeRel localsRel
  intro clock
  rcases run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
    (listToNumSetHOLExact (List.range params.length)) body)
    {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} with ⟨result,post⟩
  have complete := bodyComplete clock
  rw [run] at complete
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name params body found
  subst len
  have h := optimise_callee_crep_bound _ bodyShape
    ({decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}) post result
    body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) B loc (List.range params.length)
    (by simpa [decClock] using table) (by simpa [decClock,ocompileHOLExact] using hcode) run complete (bodyBound clock)
  simpa [ocompileHOLExact,decClock] using h.2

/-- The unoptimized callee induction bounds its actual compiled returning call. -/
theorem compiledReturningCall_optimised_bound_from_body {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL 64)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (source : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (values : List (HolWordLab 64)) (params : List Nat) (body : CrepProgHOL 64) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup) (namesDistinct : names.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : LoopTableSupported target.code)
    (bodyShape : SimpleLoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body))
    (bodyComplete : source.clock ≠ 0 → CompleteLoopResult
      (evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
        {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}).1)
    (bodyBound : source.clock ≠ 0 → LoopSteps.steps
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) target ≤
      max (2 * args.length + 4) ((loopCodeWeight target.code+2)*(2*B+1)) * CrepSteps.steps (.call (some (names,none)) name args) source := by
  apply compiledReturningCall_bound_from_body ctxt live name args shape names returnNames mapped source target values params body
    ((loopCodeWeight target.code+2)*(2*B+1)) hargs found arity distinct namesDistinct stateRel memRel globalsRel codeRel localsRel
  intro clock
  rcases run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
    (listToNumSetHOLExact (List.range params.length)) body)
    {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} with ⟨result,post⟩
  have complete := bodyComplete clock
  rw [run] at complete
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name params body found
  subst len
  have h := optimise_callee_crep_bound _ bodyShape
    ({decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}) post result
    body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) B loc (List.range params.length)
    (by simpa [decClock] using table) (by simpa [decClock,ocompileHOLExact] using hcode) run complete (bodyBound clock)
  simpa [ocompileHOLExact,decClock] using h.2

/-- A scalar-argument tail call lifts the unoptimized callee induction through
the actual optimizer and the whole Loop code table. -/
theorem compiledScalarTail_optimised_bound_from_body {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL 64)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (values : List (HolWordLab 64)) (params : List Nat) (body : CrepProgHOL 64) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : LoopTableSupported target.code)
    (bodyShape : SimpleLoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body))
    (bodyComplete : ∀ st : LoopSemStateFiniteExact 64 σ,
      crepToLoopStateRelExact source st → crepToLoopMemRelHOLExact source.memory st.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals st.globals → crepToLoopCodeRelExact ctxt source.code st.code →
      st.code = target.code → source.clock ≠ 0 → CompleteLoopResult
      (evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
        {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}).1)
    (bodyBound : ∀ st : LoopSemStateFiniteExact 64 σ,
      crepToLoopStateRelExact source st → crepToLoopMemRelHOLExact source.memory st.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals st.globals → crepToLoopCodeRelExact ctxt source.code st.code →
      st.code = target.code → source.clock ≠ 0 → LoopSteps.steps
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    let prefixCost := LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1)
    ∃ extra, extra ≤ prefixCost ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) {target with clock := target.clock+extra} ≤
        max (prefixCost + 2*args.length+3) ((loopCodeWeight target.code+2)*(2*B+1)) * CrepSteps.steps (.call none name args) source := by
  apply compiledScalarTail_bound_from_body ctxt live name args shape source target values params body
    ((loopCodeWeight target.code+2)*(2*B+1)) hargs found arity distinct stateRel memRel globalsRel codeRel localsRel
  intro st stRel stMem stGlobals stCode same clock
  rcases run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
    (listToNumSetHOLExact (List.range params.length)) body)
    {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} with ⟨result,post⟩
  have complete := bodyComplete st stRel stMem stGlobals stCode same clock
  rw [run] at complete
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := stCode.2 name params body found
  subst len
  have h := optimise_callee_crep_bound _ bodyShape
    ({decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}) post result
    body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) B loc (List.range params.length)
    (by simpa [decClock,same] using table) (by simpa [decClock,ocompileHOLExact] using hcode) run complete
    (bodyBound st stRel stMem stGlobals stCode same clock)
  simpa [ocompileHOLExact,decClock,same] using h.2
/-- A scalar-argument returning call lifts the unoptimized callee induction through
the actual optimizer and the whole Loop code table. -/
theorem compiledScalarReturning_optimised_bound_from_body {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL 64)) (shape : ∀ e ∈ args, CompiledScalar e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (source : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (values : List (HolWordLab 64)) (params : List Nat) (body : CrepProgHOL 64) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup) (namesDistinct : names.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : LoopTableSupported target.code)
    (bodyShape : SimpleLoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body))
    (bodyComplete : ∀ st : LoopSemStateFiniteExact 64 σ,
      crepToLoopStateRelExact source st → crepToLoopMemRelHOLExact source.memory st.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals st.globals → crepToLoopCodeRelExact ctxt source.code st.code →
      st.code = target.code → source.clock ≠ 0 → CompleteLoopResult
      (evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
        {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}).1)
    (bodyBound : ∀ st : LoopSemStateFiniteExact 64 σ,
      crepToLoopStateRelExact source st → crepToLoopMemRelHOLExact source.memory st.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals st.globals → crepToLoopCodeRelExact ctxt source.code st.code →
      st.code = target.code → source.clock ≠ 0 → LoopSteps.steps
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    let prefixCost := LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1)
    ∃ extra, extra ≤ prefixCost ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) {target with clock := target.clock+extra} ≤
        max (prefixCost + 2*args.length+4) ((loopCodeWeight target.code+2)*(2*B+1)) * CrepSteps.steps (.call (some (names,none)) name args) source := by
  apply compiledScalarReturning_bound_from_body ctxt live name args shape names returnNames mapped source target values params body
    ((loopCodeWeight target.code+2)*(2*B+1)) hargs found arity distinct namesDistinct stateRel memRel globalsRel codeRel localsRel
  intro st stRel stMem stGlobals stCode same clock
  rcases run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
    (listToNumSetHOLExact (List.range params.length)) body)
    {decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} with ⟨result,post⟩
  have complete := bodyComplete st stRel stMem stGlobals stCode same clock
  rw [run] at complete
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := stCode.2 name params body found
  subst len
  have h := optimise_callee_crep_bound _ bodyShape
    ({decClock st with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))}) post result
    body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) B loc (List.range params.length)
    (by simpa [decClock,same] using table) (by simpa [decClock,ocompileHOLExact] using hcode) run complete
    (bodyBound st stRel stMem stGlobals stCode same clock)
  simpa [ocompileHOLExact,decClock,same] using h.2


/-- Every table entry has the global control-node bound. -/
theorem loopTable_entry_bound (code : Spt (List Nat × HolLoopProg width))
    (loc : Nat) (params : List Nat) (body : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (codeEq : s.code = code)
    (supported : LoopTableSupported code) (found : sptLookup loc code = some (params,body)) :
    steps body s ≤ loopVisitWeight body + (loopCodeWeight code+2) * (s.clock-(evaluate body s).2.clock) := by
  have h := simpleSequence_global_bound body s (loopCodeWeight code+2) (supported loc params body found) (by simpa [codeEq] using supported) (by simp [codeEq])
    (by have w := loopCodeWeight_lookup code loc params body found; simpa [codeEq] using Nat.le_add_right_of_le w)
  simpa only [codeEq] using h

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

private theorem returning_shift_at {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool) (s final : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (extra : Nat)
    (bodyShift : ∀ values env body cut post bodyResult,
      getVars args s = some values → findCode (some loc) values s.code = some (env,body) →
      cutRes live (none,s) = (none,cut) → evaluate body {cut with locals := env} = (bodyResult,post) →
      bodyResult ≠ some .timeOut →
      steps body {{cut with locals := env} with clock := cut.clock + extra} = steps body {cut with locals := env})
    (run : evaluate (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s = (res,final))
    (nonTimeout : res ≠ some .timeOut) :
    steps (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) {s with clock := s.clock + extra} =
    steps (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  have getShift : getVars args {s with clock := s.clock + extra} = getVars args s := getVars_upd_clock s _ args
  cases get : getVars args s with
  | none =>
    rw [steps.eq_def,steps.eq_def]
    simp [getShift,get]
  | some values =>
    cases found : findCode (some loc) values s.code with
    | none =>
      rw [steps.eq_def,steps.eq_def]
      simp [getShift,get,found]
    | some pair =>
      obtain ⟨env,body⟩ := pair
      by_cases nd : names.Nodup
      · rcases cutRun : cutRes live (none,s) with ⟨cutResult,cut⟩
        cases cutResult with
        | some err =>
          have errNotTimeout : some err ≠ some .timeOut := by
            intro bad
            have whole := run
            rw [evaluate] at whole
            simp only [get,found,nd,not_true_eq_false,if_false] at whole
            rw [cutRun] at whole
            simp only [Prod.mk.injEq] at whole
            exact nonTimeout (whole.1.symm.trans bad)
          have cutShift := cutRes_add_clock live none s cut (some err) extra cutRun errNotTimeout
          rw [steps.eq_def,steps.eq_def]
          simp [getShift,get,found,nd,cutRun,cutShift]
        | none =>
          rcases bodyRun : evaluate body {cut with locals := env} with ⟨bodyResult,post⟩
          have bodyNotTimeout : bodyResult ≠ some .timeOut := by
            intro bad
            have whole := run
            rw [evaluate] at whole
            simp only [get,found,nd,not_true_eq_false,if_false] at whole
            rw [cutRun] at whole
            simp only at whole
            rw [fix_clock_evaluate,bodyRun,bad] at whole
            simp only [Prod.mk.injEq] at whole
            exact nonTimeout whole.1.symm
          have cutShift := cutRes_add_clock live none s cut none extra cutRun (by simp)
          have bodyRunShift := evaluate_add_clock_eq body {cut with locals := env} bodyResult post extra bodyRun bodyNotTimeout
          have count := bodyShift values env body cut post bodyResult get found cutRun bodyRun bodyNotTimeout
          have get' : getVars args {s with clock := s.clock + extra} = some values := by rw [getShift,get]
          have found' : findCode (some loc) values ({s with clock := s.clock + extra} : LoopSemStateFiniteExact width F).code = some (env,body) := found
          have cutShift' : cutRes live (none,{s with clock := s.clock + extra}) = (none,{cut with clock := cut.clock + extra}) := cutShift
          have bodyRunShift' : evaluate body {{cut with clock := cut.clock + extra} with locals := env} =
              (bodyResult,{post with clock := post.clock + extra}) := by simpa using bodyRunShift
          rw [steps_call_returning _ _ _ _ _ _ _ _ _ _ _ _ get' found' nd cutShift' bodyRunShift',
            steps_call_returning _ _ _ _ _ _ _ _ _ _ _ _ get found nd cutRun bodyRun]
          rw [count]
          cases bodyResult with
          | none => rfl
          | some r =>
            cases r <;> try rfl
            all_goals cases markHandler <;> cases markNormal <;> simp [steps_mark,steps_leaf]

      · rw [steps.eq_def,steps.eq_def]
        simp [getShift,get,found,nd]

set_option maxHeartbeats 5000000 in
/-- A completed run retains its exact visit count when clock is added, including nested calls. -/
theorem loopTable_steps_add_clock {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s final : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (shape : SimpleLoopSequenceSource p)
    (table : LoopTableSupported s.code) (run : evaluate p s = (res,final))
    (nonTimeout : res ≠ some .timeOut) (extra : Nat) :
    steps p {s with clock := s.clock + extra} = steps p s := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s final : LoopSemStateFiniteExact width F)
      (res : Option (LoopResultExact width)), (s.clock,sizeOf p) = x → SimpleLoopSequenceSource p →
      LoopTableSupported s.code → evaluate p s = (res,final) → res ≠ some .timeOut →
      steps p {s with clock := s.clock + extra} = steps p s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s final res hx shape table run nonTimeout
      have ih : ∀ (q : HolLoopProg width) (t u : LoopSemStateFiniteExact width F) (r : Option (LoopResultExact width)),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          SimpleLoopSequenceSource q → t.code = s.code → evaluate q t = (r,u) → r ≠ some .timeOut →
          steps q {t with clock := t.clock + extra} = steps q t := by
        intro q t u r smaller qshape same qrun qnonTimeout
        have table' : LoopTableSupported t.code := by rw [same]; exact table
        exact ih0 _ (hx ▸ smaller) q t u r rfl qshape table' qrun qnonTimeout
      clear ih0 hx
      cases shape with
      | branch h => exact branchedProgram_steps_add_clock (branch_branched h) s final res run nonTimeout extra
      | @loop live exits body h =>
        apply nestedLoop_steps_add_clock_at live exits body s final res run nonTimeout extra
        intro t u r small same trun noTime
        exact ih body t u r (Prod.Lex.left _ _ small) h same trun noTime
      | @seq a b ha hb =>
        rw [steps_seq,steps_seq]
        rcases firstRun : evaluate a s with ⟨firstRes,middle⟩
        have firstNotTimeout : firstRes ≠ some .timeOut := by
          intro bad
          have whole := run
          rw [evaluate_seq,firstRun,bad] at whole
          cases whole
          exact nonTimeout rfl
        have firstLift := evaluate_add_clock_eq a s firstRes middle extra firstRun firstNotTimeout
        rw [firstLift]
        have firstSteps := ih a s middle firstRes (Prod.Lex.right _ (by simp_wf; omega)) ha rfl firstRun firstNotTimeout
        rw [firstSteps]
        cases firstRes with
        | some r => rfl
        | none =>
          have secondRun : evaluate b middle = (res,final) := by
            rw [evaluate_seq,firstRun] at run
            exact run
          have clock := evaluate_clock a s none middle firstRun
          have code := SteppedFlapjack.LoopLiveSteps.evaluate_code a s middle none firstRun
          have secondSteps := ih b middle final res (lexLt clock (by simp_wf)) hb code secondRun nonTimeout
          simpa only using congrArg (fun n => 1 + steps a s + n) secondSteps
      | @mark q h =>
        rw [steps_mark,steps_mark]
        apply congrArg (Nat.add 1)
        exact ih q s final res (Prod.Lex.right _ (by simp_wf)) h rfl (by simpa only [evaluate] using run) nonTimeout
      | @conditional cmp r ri live a b ha hb =>
        rw [steps_ite,steps_ite]
        have sameLookup : sptLookup r ({s with clock := s.clock + extra} : LoopSemStateFiniteExact width F).locals =
            sptLookup r s.locals := rfl
        have sameImm : getVarImm ri {s with clock := s.clock + extra} = getVarImm ri s := by cases ri <;> rfl
        rw [sameLookup,sameImm]
        rcases hx : sptLookup r s.locals with _ | (x | ⟨_,_⟩) <;> try rfl
        rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> try rfl
        simp only
        have run' := run
        simp only [evaluate,hx,hy] at run'
        by_cases compare : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
        · simp only [compare,if_true] at run' ⊢
          rcases branch : evaluate a s with ⟨branchResult,branchPost⟩
          have noTimeout : branchResult ≠ some .timeOut := by
            intro bad
            rw [branch,bad] at run'
            simp only [cutRes,Prod.mk.injEq] at run'
            exact nonTimeout run'.1.symm
          have bound := ih a s branchPost branchResult (Prod.Lex.right _ (by simp_wf; omega)) ha rfl branch noTimeout
          exact congrArg (Nat.add 1) bound
        · simp only [compare,Bool.false_eq_true,if_false] at run' ⊢
          rcases branch : evaluate b s with ⟨branchResult,branchPost⟩
          have noTimeout : branchResult ≠ some .timeOut := by
            intro bad
            rw [branch,bad] at run'
            simp only [cutRes,Prod.mk.injEq] at run'
            exact nonTimeout run'.1.symm
          have bound := ih b s branchPost branchResult (Prod.Lex.right _ (by simp_wf; omega)) hb rfl branch noTimeout
          exact congrArg (Nat.add 1) bound
      | tail loc args =>
        have getShift : getVars args {s with clock := s.clock + extra} = getVars args s := getVars_upd_clock s (s.clock + extra) args
        cases get : getVars args s with
        | none =>
          rw [steps.eq_def,steps.eq_def]
          simp [getShift,get]
        | some values =>
          cases found : findCode (some loc) values s.code with
          | none =>
            rw [steps.eq_def,steps.eq_def]
            simp [getShift,get,found]
          | some pair =>
            obtain ⟨env,body⟩ := pair
            have nz : s.clock ≠ 0 := by
              intro zero
              rw [evaluate] at run
              simp [get,found,zero] at run
              exact nonTimeout run.1.symm
            rcases bodyRun : evaluate body {decClock s with locals := env} with ⟨bodyResult,post⟩
            have bodyNotTimeout : bodyResult ≠ some .timeOut := by
              intro bad
              have whole := run
              rw [evaluate] at whole
              simp [get,found,nz,bodyRun,bad] at whole
              exact nonTimeout whole.1.symm
            obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc values env body found
            have smaller : (decClock s).clock < s.clock := by simp [decClock]; omega
            have bound := ih body {decClock s with locals := env} post bodyResult
              (Prod.Lex.left _ _ smaller) (table loc params body lookup) rfl bodyRun bodyNotTimeout
            have get' : getVars args {s with clock := s.clock + extra} = some values := by rw [getShift,get]
            have found' : findCode (some loc) values ({s with clock := s.clock + extra} : LoopSemStateFiniteExact width F).code = some (env,body) := found
            have nz' : (s.clock + extra) ≠ 0 := by omega
            rw [steps_call_tail _ _ _ _ _ _ get' found' nz', steps_call_tail _ _ _ _ _ _ get found nz]
            apply congrArg (Nat.add 1)
            have clockEq : s.clock + extra - 1 = s.clock - 1 + extra := by omega
            simpa [decClock, clockEq] using bound
      | returning names live loc exc args liveOut =>
        apply returning_shift_at loc args names live liveOut exc false false s final res extra ?_ run nonTimeout
        intro values env body cut post bodyResult get found cutRun bodyRun noTime
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc values env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by
          have h := SteppedFlapjack.LoopLiveSteps.cutRes_code live none s
          rw [cutRun] at h
          exact h
        exact ih body {cut with locals := env} post bodyResult (Prod.Lex.left _ _ small)
          (table loc params body lookup) same bodyRun noTime
      | returningMarked names live loc exc args liveOut =>
        apply returning_shift_at loc args names live liveOut exc true true s final res extra ?_ run nonTimeout
        intro values env body cut post bodyResult get found cutRun bodyRun noTime
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc values env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by
          have h := SteppedFlapjack.LoopLiveSteps.cutRes_code live none s
          rw [cutRun] at h
          exact h
        exact ih body {cut with locals := env} post bodyResult (Prod.Lex.left _ _ small)
          (table loc params body lookup) same bodyRun noTime
  exact key _ p s final res rfl shape table run nonTimeout

end SteppedFlapjack.LoopLiveSteps
