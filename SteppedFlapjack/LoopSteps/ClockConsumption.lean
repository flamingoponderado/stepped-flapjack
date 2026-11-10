import SteppedFlapjack.LoopSteps.BranchedStatic

/-! Clock consumption is bounded by Loop evaluator visits. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Encoders.Asm

/-- A cut consumes at most one clock unit. -/
theorem cutRes_clock_consumed {width : Nat} [NeZero width] {F : Type}
    (live : NumSet) (res : Option (LoopResultExact width)) (s : LoopSemStateFiniteExact width F) :
    s.clock - (cutRes live (res,s)).2.clock ≤ 1 := by
  cases res with
  | some r => simp [cutRes]
  | none =>
    simp only [cutRes]
    cases hc : cutState live s with
    | none => simp
    | some t =>
      simp only
      have h := cutState_clock hc
      split <;> simp [decClock] <;> omega

/-- Every direct leaf consumes at most one clock unit. -/
theorem directLeaf_clock_consumed {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : DirectLeaf p) (s t : LoopSemStateFiniteExact width F)
    (r : Option (LoopResultExact width)) (run : evaluate p s = (r,t)) : s.clock - t.clock ≤ 1 := by
  cases shape <;> rw [evaluate] at run
  all_goals repeat' first | split at run | cases run
  all_goals try have hm := memStore_clock (by assumption)
  all_goals try have ha := loopArith_clock (by assumption)
  all_goals simp_all [setVar,setGlobals,decClock,LoopSemStateFiniteExact.callEnv]
  all_goals omega

/-- Branch-program source clock consumption is bounded by its actual visits. -/
theorem branchedProgram_clock_consumed {width : Nat} [NeZero width] {F : Type}
    {p : HolLoopProg width} (shape : BranchedProgram p)
    (s t : LoopSemStateFiniteExact width F) (r : Option (LoopResultExact width))
    (run : evaluate p s = (r,t)) : s.clock - t.clock ≤ steps p s := by
  induction shape generalizing s t r with
  | @leaf p leaf =>
    have h := directLeaf_clock_consumed leaf s t r run
    have one : steps p s = 1 := by apply steps_leaf; cases leaf <;> rfl
    omega
  | @mark p shape ih =>
    rw [steps_mark]
    have he : evaluate p s = (r,t) := by simpa only [evaluate] using run
    have h := ih s t r he
    omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstBound := iha s middle out first
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have secondBound := ihb middle t r run
      have secondClock := evaluate_clock b middle r t run
      omega
    | some x =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega
  | @ite cmp reg ri live a b ha hb iha ihb =>
    rw [steps_ite]
    simp only [evaluate] at run
    rcases hx : sptLookup reg s.locals with _ | (x | ⟨_,_⟩) <;>
      rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only [hx,hy] at run ⊢ <;>
      try (cases run; simp; done)
    by_cases hcmp : wordCmpHOL cmp x y = true
    · simp only [hcmp,if_true] at run ⊢
      rcases branch : evaluate a s with ⟨br,post⟩
      have hb := iha s post br branch
      have hc := cutRes_clock_consumed live br post
      have he := evaluate_clock a s br post branch
      rw [branch] at run
      have ht : (cutRes live (br,post)).2.clock = t.clock := by rw [run]
      rw [ht] at hc
      omega
    · simp only [hcmp,Bool.false_eq_true,if_false] at run ⊢
      rcases branch : evaluate b s with ⟨br,post⟩
      have hb := ihb s post br branch
      have hc := cutRes_clock_consumed live br post
      have he := evaluate_clock b s br post branch
      rw [branch] at run
      have ht : (cutRes live (br,post)).2.clock = t.clock := by rw [run]
      rw [ht] at hc
      omega

/-- Combine consumption bounds for a reached callee and its normal continuation. -/
theorem returning_clock_consumed {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live liveOut : NumSet)
    (exception : Nat) (handler normal : HolLoopProg width)
    (s cut post middle final : LoopSemStateFiniteExact width F)
    (values returned : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (out result : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (some (.result returned),post))
    (arity : returned.length = names.length)
    (normalRun : evaluate normal (setVars names returned {post with locals := cut.locals}) = (out,middle))
    (finalCut : cutRes liveOut (out,middle) = (result,final))
    (bodyBound : cut.clock - post.clock ≤ 2 * steps body {cut with locals := env})
    (normalBound : post.clock - middle.clock ≤
      2 * steps normal (setVars names returned {post with locals := cut.locals})) :
    evaluate (.call (some (names,live)) dest args (some (exception,handler,normal,liveOut))) s = (result,final) ∧
    s.clock - final.clock ≤ 2 * steps (.call (some (names,live)) dest args
      (some (exception,handler,normal,liveOut))) s := by
  have execution := evaluate_call_returning_success dest args names live liveOut exception handler normal s cut post values returned env body get found distinct cutRun bodyRun arity
  rw [normalRun,finalCut] at execution
  refine ⟨execution, ?_⟩
  have count := steps_call_returning dest args names live (some (exception,handler,normal,liveOut))
    s cut post values env body (some (.result returned)) get found distinct cutRun bodyRun
  simp only [arity,ne_eq,not_true_eq_false,if_false] at count
  have first := cutRes_clock_consumed live none s
  have last := cutRes_clock_consumed liveOut out middle
  rw [cutRun] at first
  rw [finalCut] at last
  have firstLe := cutRes_clock_le live (none,s)
  have lastLe := cutRes_clock_le liveOut (out,middle)
  rw [cutRun] at firstLe
  rw [finalCut] at lastLe
  have bodyLe := evaluate_clock body {cut with locals := env} (some (.result returned)) post bodyRun
  have normalLe := evaluate_clock normal (setVars names returned {post with locals := cut.locals}) out middle normalRun
  simp only [setVars] at normalLe
  simp only at first last firstLe lastLe bodyLe
  rw [count]
  omega

end SteppedFlapjack.LoopSteps
