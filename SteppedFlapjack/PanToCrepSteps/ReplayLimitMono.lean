import SteppedFlapjack.CrepToLoopSteps.DeclRiscVInputs
import SteppedFlapjack.StackRemoveSteps.CostMono

/-! Monotonic replay limits for independently established source bounds. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordToStackSteps Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect

/-- Increasing a Crep entry-step bound cannot reduce the declaration-loop
replay limit passed to the Loop compiler proof. -/
theorem branchTailDeclLoopLimit_mono
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (name : Nat) (e : CrepExpHOL 64) (init : CrepProgHOL 64)
    (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64) {first second : Nat}
    (bound : first ≤ second) :
    branchTailDeclLoopLimit ctxt live callee entryInit name e init condition body tail first ≤
      branchTailDeclLoopLimit ctxt live callee entryInit name e init condition body tail second := by
  dsimp only [branchTailDeclLoopLimit]
  gcongr

/-- Increasing the Loop step bound cannot reduce the Word replay clock. -/
theorem tailWordReplayLimit_mono (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) {first second : Nat} (bound : first ≤ second) :
    tailWordReplayLimit p ctxt labels code first ≤ tailWordReplayLimit p ctxt labels code second := by
  unfold tailWordReplayLimit
  gcongr

/-- Increasing the Loop step bound cannot reduce the Stack replay clock. -/
theorem tailStackReplayLimit_mono (ac : AsmConfigExact 64) (count name alg regCount : Nat)
    (col : Option (Spt Nat)) (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) {first second : Nat} (bound : first ≤ second) :
    tailStackReplayLimit ac count name alg regCount col p ctxt labels code first ≤
      tailStackReplayLimit ac count name alg regCount col p ctxt labels code second := by
  dsimp only [tailStackReplayLimit]
  have wordBound := tailWordReplayLimit_mono p ctxt labels code bound
  gcongr

/-- The compiled call-sequence cost grows monotonically with its clock limit. -/
theorem callSequenceCost_mono {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (code : Spt (HolProg width)) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    {first second : Nat} (bound : first ≤ second) :
    callSequenceCost ac first code p bs kf ≤ callSequenceCost ac second code p bs kf := by
  conv_lhs => rw [callSequenceCost.eq_def]
  conv_rhs => rw [callSequenceCost.eq_def]
  split
  · exact SteppedFlapjack.StackAllocSteps.linearLoopCost_mono _ bound
  · cases hp : p <;> try rfl
    case seq a b =>
      simp only
      have firstBound := callSequenceCost_mono ac code a bs kf bound
      have secondBound := callSequenceCost_mono ac code b (compNative ac false a bs kf).2 kf bound
      omega
    case call ret dest args handler =>
      cases ret with
      | none =>
        cases handler with
        | none =>
          simp only
          have h := loopCodeCost_mono code bound
          omega
        | some h => rfl
      | some r => exact returningChainCost_mono code _ bound
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- The full finite-oracle machine-cost expression is monotone in the Stack
replay limit. Changing the clock does not change its code or oracle budget. -/
theorem machineCost_mono {C F : Type}
    (ac : AsmConfigExact 64) (stackCode : Spt (HolProg 64))
    (out : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    (bounds : BitVec 64 × BitVec 64) (program : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) (uniform labFactor flattenFactor : Nat)
    {first second : Nat} (h : first ≤ second) :
    labFactor * (flattenFactor *
      (computedRunCost bounds (uniform * (3 + callSequenceCost ac first stackCode out bs kf)) program
        {state with clock := first+1} * (uniform * (3 + callSequenceCost ac first stackCode out bs kf)) + 4)) ≤
    labFactor * (flattenFactor *
      (computedRunCost bounds (uniform * (3 + callSequenceCost ac second stackCode out bs kf)) program
        {state with clock := second+1} * (uniform * (3 + callSequenceCost ac second stackCode out bs kf)) + 4)) := by
  have calls := callSequenceCost_mono ac stackCode out bs kf h
  have stepBudget : uniform * (3 + callSequenceCost ac first stackCode out bs kf) ≤
      uniform * (3 + callSequenceCost ac second stackCode out bs kf) := by gcongr
  have factor := computedRunCost_mono bounds program state stepBudget
  rw [computedRunCost_clock,computedRunCost_clock]
  exact Nat.mul_le_mul_left labFactor (Nat.mul_le_mul_left flattenFactor
    (Nat.add_le_add_right (Nat.mul_le_mul factor stepBudget) 4))

end SteppedFlapjack.PanToCrepSteps
