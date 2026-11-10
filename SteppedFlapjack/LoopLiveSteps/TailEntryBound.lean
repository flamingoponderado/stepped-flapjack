import SteppedFlapjack.LoopLiveSteps.TailEntryShape
import SteppedFlapjack.LoopLiveSteps.Consumption
import SteppedFlapjack.LoopSteps.BranchedClock

/-! A successful tail-entry prefix has not reached any tail call. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- A direct tail call always produces a result, including failure and timeout. -/
theorem directTail_ne_none (loc : Nat) (args : List Nat) (s : LoopSemStateFiniteExact width F) :
    (evaluate (.call none (some loc) args none) s).1 ≠ none := by
  rw [evaluate]
  rcases hargs : getVars args s with _ | values
  · simp
  · simp only
    rcases hfind : findCode (some loc) values s.code with _ | ⟨env,body⟩
    · simp
    · simp only [Option.isSome_none,Bool.false_eq_true,if_false]
      by_cases hz : s.clock = 0
      · simp [hz]
      · simp only [hz, dite_false]
        rcases h : evaluate body {decClock s with locals := env} with ⟨out,post⟩
        cases out with
        | none => simp
        | some r => cases r <;> simp

/-- A tail-entry execution that returns no result has visited only its own
syntax; a reached tail call would have produced a result. -/
theorem tailEntry_none_static {p : HolLoopProg width} (shape : TailEntryShape p)
    (s post : LoopSemStateFiniteExact width F) (run : evaluate p s = (none,post)) :
    steps p s ≤ sizeOf p := by
  induction shape generalizing s post with
  | branch h => exact branchedProgram_static_bound (branch_branched h) s
  | call loc => exact ((directTail_ne_none loc [] s) (by rw [run])).elim
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | none =>
      simp only at run ⊢
      have h1 := iha s middle first
      have h2 := ihb middle post run
      simp_wf
      omega
    | some r => simp only [Prod.mk.injEq,Option.some_ne_none] at run; exact run.1.elim
  | @mark p hp ih =>
    rw [steps_mark]
    have inner : evaluate p s = (none,post) := by simpa only [evaluate] using run
    have h := ih s post inner
    simp_wf
    omega

/-- A no-result entry prefix consumes at most one clock unit per visited node;
all reached computation is in the call-free branch fragment. -/
theorem tailEntry_none_consumed {p : HolLoopProg width} (shape : TailEntryShape p)
    (s post : LoopSemStateFiniteExact width F) (run : evaluate p s = (none,post)) :
    s.clock-post.clock ≤ steps p s := by
  induction shape generalizing s post with
  | branch h => exact branchedProgram_clock_consumed (branch_branched h) s post none run
  | call loc => exact ((directTail_ne_none loc [] s) (by rw [run])).elim
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | none =>
      simp only at run ⊢
      have h1 := iha s middle first
      have h2 := ihb middle post run
      have c1 := evaluate_clock a s none middle first
      have c2 := evaluate_clock b middle none post run
      omega
    | some r => simp only [Prod.mk.injEq,Option.some_ne_none] at run; exact run.1.elim
  | @mark p hp ih =>
    rw [steps_mark]
    have inner : evaluate p s = (none,post) := by simpa only [evaluate] using run
    have h := ih s post inner
    omega

/-- Adding unused clock does not change the visit count of an entry prefix
that finishes without a result. -/
theorem tailEntry_none_steps_add_clock {p : HolLoopProg width} (shape : TailEntryShape p)
    (s post : LoopSemStateFiniteExact width F) (run : evaluate p s = (none,post)) (extra : Nat) :
    steps p {s with clock := s.clock+extra} = steps p s := by
  induction shape generalizing s post with
  | branch h => exact branchedProgram_steps_add_clock (branch_branched h) s post none run (by simp) extra
  | call loc => exact ((directTail_ne_none loc [] s) (by rw [run])).elim
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | none =>
      simp only at run ⊢
      have firstShift := evaluate_add_clock_eq a s none middle extra first (by simp)
      have firstSteps := iha s middle first
      have secondSteps := ihb middle post run
      rw [firstShift,firstSteps]
      simp only
      rw [secondSteps]
    | some r => simp only [Prod.mk.injEq,Option.some_ne_none] at run; exact run.1.elim
  | @mark p hp ih =>
    rw [steps_mark,steps_mark]
    have inner : evaluate p s = (none,post) := by simpa only [evaluate] using run
    rw [ih s post inner]

/-- For a successful argument and code lookup, a direct tail call's visits are
bounded by callee syntax times the clock consumed by the call. -/
theorem directTail_consumption_bound (loc : Nat) (args : List Nat) (values : List (WordLocW width)) (env : Spt (WordLocW width)) (s post : LoopSemStateFiniteExact width F)
    (body : HolLoopProg width) (shape : LoopSequenceSource body) (result : Option (LoopResultExact width))
    (get : getVars args s = some values) (lookup : findCode (some loc) values s.code = some (env,body)) (clock : s.clock ≠ 0)
    (run : evaluate (.call none (some loc) args none) s = (result,post)) :
    steps (.call none (some loc) args none) s ≤ (1 + sizeOf body) * (s.clock-post.clock+1) := by
  have count := steps_call_tail (some loc) args s values env body get lookup clock
  rcases bodyRun : evaluate body {decClock s with locals := env} with ⟨out,final⟩
  have bound := sequence_consumption_bound shape {decClock s with locals := env} final out bodyRun
  have bodyClock := evaluate_clock body {decClock s with locals := env} out final bodyRun
  have execution := run
  rw [evaluate] at execution
  simp only [get,lookup,Option.isSome_none,Bool.false_eq_true,if_false,
    clock,dite_false] at execution
  rw [bodyRun] at execution
  simp only [decClock] at bound bodyClock count
  cases out with
  | none =>
    simp only [Prod.mk.injEq] at execution
    obtain ⟨_,rfl⟩ := execution
    have budget : s.clock-1-final.clock+1 ≤ s.clock-final.clock+1 := by omega
    have scaled := Nat.mul_le_mul_left (sizeOf body) budget
    rw [count]
    nlinarith
  | some r =>
    cases r <;> simp only [Prod.mk.injEq] at execution <;> obtain ⟨_,rfl⟩ := execution
    all_goals have budget : s.clock-1-final.clock+1 ≤ s.clock-final.clock+1 := by omega
    all_goals have scaled := Nat.mul_le_mul_left (sizeOf body) budget
    all_goals rw [count]
    all_goals nlinarith

/-- Clock consumed by a successful direct tail call is bounded by twice its actual visits. -/
theorem directTail_clock_consumed (loc : Nat) (args : List Nat) (values : List (WordLocW width)) (env : Spt (WordLocW width)) (s post : LoopSemStateFiniteExact width F)
    (body : HolLoopProg width) (shape : LoopSequenceSource body) (result : Option (LoopResultExact width))
    (get : getVars args s = some values) (lookup : findCode (some loc) values s.code = some (env,body)) (clock : s.clock ≠ 0)
    (run : evaluate (.call none (some loc) args none) s = (result,post)) :
    s.clock-post.clock ≤ 2 * steps (.call none (some loc) args none) s := by
  have count := steps_call_tail (some loc) args s values env body get lookup clock
  rcases bodyRun : evaluate body {decClock s with locals := env} with ⟨out,final⟩
  have bound := sequence_consumed shape {decClock s with locals := env} final out bodyRun
  have bodyClock := evaluate_clock body {decClock s with locals := env} out final bodyRun
  have execution := run
  rw [evaluate] at execution
  simp only [get,lookup,Option.isSome_none,Bool.false_eq_true,if_false,
    clock,dite_false] at execution
  rw [bodyRun] at execution
  simp only [decClock] at bound bodyClock count
  cases out with
  | none =>
    simp only [Prod.mk.injEq] at execution
    obtain ⟨_,rfl⟩ := execution
    rw [count]
    omega
  | some r =>
    cases r <;> simp only [Prod.mk.injEq] at execution <;> obtain ⟨_,rfl⟩ := execution <;>
      rw [count] <;> omega

end SteppedFlapjack.LoopLiveSteps
