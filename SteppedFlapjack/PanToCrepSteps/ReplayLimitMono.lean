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
  · exact loopOnlyCost_mono _ bound
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

/-- A larger independently established source limit gives a larger compiled
call-sequence budget through both replay-clock transformations. -/
theorem declSource_callSequenceCost_mono
    (crepCtxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (localVar : Nat) (value : CrepExpHOL 64)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (loop : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (stackCode : Spt (HolProg 64))
    (out : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    {first second : Nat} (bound : first ≤ second) :
    callSequenceCost ac (tailStackReplayLimit ac count name alg regCount col loop ctxt labels code
      (branchTailDeclLoopLimit crepCtxt live callee entryInit localVar value init condition body tail first)) stackCode out bs kf ≤
    callSequenceCost ac (tailStackReplayLimit ac count name alg regCount col loop ctxt labels code
      (branchTailDeclLoopLimit crepCtxt live callee entryInit localVar value init condition body tail second)) stackCode out bs kf := by
  apply callSequenceCost_mono
  apply tailStackReplayLimit_mono
  exact branchTailDeclLoopLimit_mono crepCtxt live callee entryInit localVar value init condition body tail bound

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

/-- A larger declaration-source bound yields a larger complete finite-oracle
machine-cost expression for the same compiled program and initial data. -/
theorem declSource_machineCost_mono {C F : Type}
    (crepCtxt : CrepToLoopContextExact) (live : NumSet) (callee : MlString)
    (entryInit : CrepProgHOL 64) (localVar : Nat) (value : CrepExpHOL 64)
    (init : CrepProgHOL 64) (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (loop : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (stackCode : Spt (HolProg 64))
    (out : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    (bounds : BitVec 64 × BitVec 64) (program : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) (uniform labFactor flattenFactor : Nat)
    {first second : Nat} (h : first ≤ second) :
    let clock := fun n => tailStackReplayLimit ac count name alg regCount col loop ctxt labels code
      (branchTailDeclLoopLimit crepCtxt live callee entryInit localVar value init condition body tail n)
    let cost := fun n => uniform * (3 + callSequenceCost ac (clock n) stackCode out bs kf)
    labFactor * (flattenFactor *
      (computedRunCost bounds (cost first) program {state with clock := clock first+1} * cost first + 4)) ≤
    labFactor * (flattenFactor *
      (computedRunCost bounds (cost second) program {state with clock := clock second+1} * cost second + 4)) := by
  apply machineCost_mono
  apply tailStackReplayLimit_mono
  exact branchTailDeclLoopLimit_mono crepCtxt live callee entryInit localVar value init condition body tail h

/-- The monotone machine expression applies to the actual Stack-allocation
initial state used by the RISC-V compilation theorem. -/
theorem machineCost_Tgt_mono {C F : Type}
    (ac : AsmConfigExact 64) (stackCode : Spt (HolProg 64))
    (out : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat) (kf : Nat × Nat × Nat)
    (bounds : BitVec 64 × BitVec 64) (program : HolProg 64)
    (state : StackSemStateFiniteExact 64 C F) (anything : WordSemGcFun 64)
    (cr : CompileFn 64 C) (config : DataToWord.Config) (uniform labFactor flattenFactor : Nat)
    {first second : Nat} (h : first ≤ second) :
    labFactor * (flattenFactor *
      (computedRunCost bounds (uniform * (3 + callSequenceCost ac first stackCode out bs kf)) program
        (Tgt anything cr config {state with clock := first+1} 0 state.regs) *
        (uniform * (3 + callSequenceCost ac first stackCode out bs kf)) + 4)) ≤
    labFactor * (flattenFactor *
      (computedRunCost bounds (uniform * (3 + callSequenceCost ac second stackCode out bs kf)) program
        (Tgt anything cr config {state with clock := second+1} 0 state.regs) *
        (uniform * (3 + callSequenceCost ac second stackCode out bs kf)) + 4)) := by
  simpa only [Tgt,Nat.add_zero] using
    machineCost_mono ac stackCode out bs kf bounds program (Tgt anything cr config state 0 state.regs)
      uniform labFactor flattenFactor h

end SteppedFlapjack.PanToCrepSteps
