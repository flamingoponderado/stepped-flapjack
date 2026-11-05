import SteppedFlapjack.StackSteps.Defs
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open SteppedFlapjack.StackSteps

/-- A simulation with a bound on the target's fine-grained steps. -/
def SimulationWithin {width : Nat} [NeZero width] {C F : Type}
    (compiled : HolProg width) (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (budget : Nat) : Prop :=
  ∃ clock targetState stackSpace,
    stateRel info post targetState ∧
    evaluate (compiled, { target with clock := target.clock + clock }) =
      (result, { targetState with stackSpace := stackSpace }) ∧
    (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
      stackSpace = targetState.stackSpace) ∧
    steps (compiled, { target with clock := target.clock + clock }) ≤ budget

/-- Both raw-call compiler modes leave a nonrecursive statement unchanged. -/
theorem compileLeaf {width : Nat} [NeZero width] (info : Spt Nat) (p : HolProg width)
    (hp : isRecursive p = false) : comp info p = p ∧ compTop info p = p := by
  cases p <;> simp_all [isRecursive, comp, compTop]

/-- The raw-call optimization preserves each nonrecursive statement in one step. -/
theorem leafWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (r : Option (StackSemResult width))
    (hp : isRecursive p = false)
    (h : evaluate (p, source) = (r, post) ∧ r ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info p) info target post r (steps (p, source)) ∧
    SimulationWithin (comp info p) info target post r (steps (p, source)) := by
  obtain ⟨ht, hc⟩ := FullCompCorrect.compCorrect p source target info r post h
  obtain ⟨hcEq, htEq⟩ := compileLeaf info p hp
  rw [steps_leaf p source hp]
  constructor
  · obtain ⟨ck, t, space, hrel, he, hspace⟩ := ht
    refine ⟨ck, t, space, hrel, he, hspace, ?_⟩
    rw [htEq, steps_leaf p _ hp]
  · obtain ⟨ck, t, space, hrel, he, hspace⟩ := hc
    refine ⟨ck, t, space, hrel, he, hspace, ?_⟩
    rw [hcEq, steps_leaf p _ hp]

end SteppedFlapjack.StackRawCallSteps
