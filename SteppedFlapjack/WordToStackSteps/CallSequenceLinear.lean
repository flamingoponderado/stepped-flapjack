import SteppedFlapjack.WordToStackSteps.CallSequenceCost
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
namespace SteppedFlapjack.WordToStackSteps

variable {width : Nat} [NeZero width]

/-- The linear loop cost scales exactly with its clock. -/
theorem linearCost_scale (k : Nat) (p : HolProg width) :
    linearLoopCost k p = linearLoopCost 0 p * (k+1) := by simp [linearLoopCost]

/-- A code table maximum is linear in the clock. -/
theorem loopCodeCost_scale (k : Nat) (code : Spt (HolProg width)) :
    loopCodeCost k code ≤ loopCodeCost 0 code * (k+1) := by
  have aux (entries : List (Nat × HolProg width)) :
      maxListNat (entries.map (fun e => linearLoopCost k e.2)) ≤
        maxListNat (entries.map (fun e => linearLoopCost 0 e.2)) * (k+1) := by
    induction entries with
    | nil => simp [maxListNat]
    | cons e es ih =>
      simp only [List.map_cons,maxListNat]
      rw [max_le_iff]
      constructor
      · rw [linearCost_scale]
        exact Nat.mul_le_mul_right _ (Nat.le_max_left _ _)
      · exact ih.trans (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
  exact aux (sptToAList code)

/-- Handler costs are linear in the clock. -/
theorem handlerCost_scale (k : Nat) (h : Option (HolProg width × Nat × Nat)) :
    handlerCost k h ≤ handlerCost 0 h * (k+1) := by
  cases h with
  | none => simp [handlerCost]
  | some v => rcases v with ⟨p,a,b⟩; exact (linearCost_scale k p).le

/-- Returning-call costs are linear in the clock. -/
theorem returningCost_scale (k : Nat) (code : Spt (HolProg width)) (p : HolProg width) :
    returningChainCost k code p ≤ returningChainCost 0 code p * (k+1) := by
  cases hp : p <;> try simp [returningChainCost]
  case seq a b =>
    have ha := linearCost_scale k a
    have hb := returningCost_scale k code b
    nlinarith
  case call ret dest handler =>
    cases ret with
    | none => simp [returningChainCost]
    | some r =>
      rcases r with ⟨body,link,l1,l2⟩
      simp only [returningChainCost]
      have hc := loopCodeCost_scale k code
      have hr := linearCost_scale k body
      have hh := handlerCost_scale k handler
      nlinarith
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- The shared call-sequence cost is linear in the clock. -/
theorem callCost_scale (ac : AsmConfigExact width) (limit : Nat) (code : Spt (HolProg width))
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    callSequenceCost ac limit code p bs kf ≤ callSequenceCost ac 0 code p bs kf * (limit+1) := by
  conv_lhs => rw [callSequenceCost.eq_def]
  conv_rhs => rw [callSequenceCost.eq_def]
  split
  · exact (linearCost_scale limit _).le
  · cases hp : p <;> try simp
    case seq a b =>
      have ha := callCost_scale ac limit code a bs kf
      have hb := callCost_scale ac limit code b (compNative ac false a bs kf).2 kf
      nlinarith
    case call ret dest args handler =>
      cases ret with
      | none =>
        cases handler with
        | none =>
          simp only
          have h := loopCodeCost_scale limit code
          nlinarith
        | some h => simp
      | some r => exact returningCost_scale limit code _
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

end SteppedFlapjack.WordToStackSteps
