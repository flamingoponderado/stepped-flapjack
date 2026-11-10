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


/-- Linear structural cost at a uniform clock limit. -/
def linearLoopCost (k : Nat) (p : HolProg width) : Nat := stackControlWeight p * (k+1)

/-- Every call-free Stack program obeys the linear cost at any larger clock. -/
theorem linearLoopCostBound (k : Nat) (p : HolProg width) (shape : loopOnly p = true) :
    ClockBound (C := C) (F := F) k p (linearLoopCost k p) := by
  intro s clock
  exact (stackControl_clock_bound p shape s).trans (Nat.mul_le_mul_left _ (by omega))

/-- The linear structural cost is monotone in its clock limit. -/
theorem linearLoopCost_mono (p : HolProg width) {lo hi : Nat} (h : lo ≤ hi) :
    linearLoopCost lo p ≤ linearLoopCost hi p :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)

/-- At zero clock the original and linear structural costs agree. -/
theorem linearLoopCost_zero (p : HolProg width) : linearLoopCost 0 p = loopOnlyCost 0 p := by
  cases hp : p <;> try rfl
  case seq a b =>
    have ha := linearLoopCost_zero a
    have hb := linearLoopCost_zero b
    simp only [linearLoopCost,stackControlWeight,loopOnlyCost,Nat.zero_add,Nat.mul_one] at ha hb ⊢
    omega
  case ite cmp r ri a b =>
    have ha := linearLoopCost_zero a
    have hb := linearLoopCost_zero b
    simp only [linearLoopCost,stackControlWeight,loopOnlyCost,Nat.zero_add,Nat.mul_one] at ha hb ⊢
    omega
  case loop a =>
    have ha := linearLoopCost_zero a
    simp only [linearLoopCost,stackControlWeight,loopOnlyCost,Nat.zero_add,Nat.mul_one] at ha ⊢
    omega
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

end SteppedFlapjack.StackAllocSteps
