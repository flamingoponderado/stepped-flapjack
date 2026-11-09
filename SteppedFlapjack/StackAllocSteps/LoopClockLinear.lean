import SteppedFlapjack.StackAllocSteps.CollectorStructural
open Flapjack Flapjack.StackSemControl Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
namespace SteppedFlapjack.StackAllocSteps

variable {width : Nat} [NeZero width] {C F : Type}

/-- Executable number of structural control nodes in a Stack program. -/
def stackControlWeight : HolProg width → Nat
  | .seq a b | .ite _ _ _ a b => 1 + stackControlWeight a + stackControlWeight b
  | .loop a => 1 + stackControlWeight a
  | _ => 1

set_option maxHeartbeats 2000000 in
/-- A call-free Stack execution is linear in the clock it consumes, including nested loops. -/
theorem stackControl_consumption_bound (p : HolProg width) (h : loopOnly p = true)
    (s : StackSemStateFiniteExact width C F) :
    steps (p,s) ≤ stackControlWeight p * (s.clock - (evaluate (p,s)).2.clock + 1) := by
  cases hp : p <;> rw [hp] at h <;> simp only [loopOnly] at h <;> try contradiction
  case seq a b =>
    simp only [Bool.and_eq_true] at h
    have ha := stackControl_consumption_bound a h.1 s
    rw [steps_seq, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    rcases run : evaluate (a,s) with ⟨result,mid⟩
    simp only [run] at ha ⊢
    cases result with
    | some r => simp only [stackControlWeight]; nlinarith
    | none =>
      have hb := stackControl_consumption_bound b h.2 mid
      have ca := StackSemEvaluateClock.evaluateClock a s none mid run
      rcases runb : evaluate (b,mid) with ⟨result,post⟩
      have cb := StackSemEvaluateClock.evaluateClock b mid result post runb
      simp only [runb] at hb ⊢
      have spent : s.clock - mid.clock + (mid.clock - post.clock) = s.clock - post.clock := by omega
      simp only [stackControlWeight]
      nlinarith
  case ite cmp r ri a b =>
    simp only [Bool.and_eq_true] at h
    have ha := stackControl_consumption_bound a h.1 s
    have hb := stackControl_consumption_bound b h.2 s
    rw [steps_ite, evaluate_ite]
    simp only [stackControlWeight]
    cases hx : getVar r s with
    | none => simp; omega
    | some x =>
      cases hy : StackSemStateOps.getVarImm (ri.toWordRegImm) s with
      | none => simp; omega
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]; omega
        | some v =>
          cases v <;> simp [hv] <;> nlinarith
  case loop body =>
    induction hc : s.clock using Nat.strongRecOn generalizing s with
    | _ clock rec =>
      have hbody := stackControl_consumption_bound body h s
      rw [steps_loop, evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]
      rcases run : evaluate (body,s) with ⟨result,post⟩
      have hclock := StackSemEvaluateClock.evaluateClock body s result post run
      simp only [run,hc] at hbody ⊢
      rw [hc] at hclock
      by_cases cont : contLoop result
      · by_cases hz : post.clock = 0
        · simp [cont,hz,emptyEnv,stackControlWeight] at *
          nlinarith
        · have smaller : (decClock post).clock < clock := by simp [decClock]; omega
          have rest := rec _ smaller (decClock post) rfl
          rcases hfinal : evaluate (.loop body,decClock post) with ⟨res,final⟩
          have finalClock := StackSemEvaluateClock.evaluateClock (.loop body) (decClock post) res final hfinal
          have spent : clock - final.clock = (clock-post.clock) + (post.clock-1-final.clock) + 1 := by
            simp only [decClock] at finalClock
            omega
          rw [hfinal] at rest
          simp only [stackControlWeight] at rest
          change steps (.loop body,decClock post) ≤ (1+stackControlWeight body)*(post.clock-1-final.clock+1) at rest
          simp [cont,hz,stackControlWeight]
          nlinarith
      · simp [cont,stackControlWeight]
        nlinarith
  all_goals
    rw [steps_leaf _ _ rfl]
    simp only [stackControlWeight]
    omega
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- The same bound expressed using the initial clock. -/
theorem stackControl_clock_bound (p : HolProg width) (h : loopOnly p = true)
    (s : StackSemStateFiniteExact width C F) :
    steps (p,s) ≤ stackControlWeight p * (s.clock+1) :=
  (stackControl_consumption_bound p h s).trans (Nat.mul_le_mul_left _ (by omega))

end SteppedFlapjack.StackAllocSteps
