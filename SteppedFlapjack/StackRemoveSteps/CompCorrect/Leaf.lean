import SteppedFlapjack.StackRemoveSteps.CodeBounds

/-! The non-recursive case of the step-counted stack removal simulation. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectLeafWithinSteps
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) (B K : Nat)
    (storeConstsBound : ∀ (temporary bitmap : Nat) (stub : Option Nat)
      (source target : StackSemStateFiniteExact width C F),
      stateRelHOL jump bounds pointer source target →
      steps (comp jump bounds pointer (.storeConsts temporary bitmap stub), target) ≤
        leafCost B bounds (.storeConsts temporary bitmap stub))
    (leaf : isRecursive program = false) (cost : leafCost B bounds program ≤ K)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer program, {target with clock := clock + target.clock}) ≤
        K * steps (program, source) := by
  obtain ⟨clock, postTarget, run, postRelation⟩ :=
    Flapjack.Compiler.Backend.StackRemove.CompCorrect.Assembly.compCorrect
      program source result postSource target pointer bounds jump hypothesis
  refine ⟨clock, postTarget, run, postRelation, ?_⟩
  have relation := RelationLaws.stateRelWithClock jump bounds pointer (clock + target.clock)
    source target hypothesis.2.2.1
  have bound := steps_comp_leaf_le jump bounds pointer B program
    {target with clock := clock + target.clock} storeConstsBound
    {source with clock := clock + target.clock} relation leaf
  have hs : steps (program, source) = 1 := steps_leaf program source leaf
  rw [hs, Nat.mul_one]
  exact bound.trans cost

end SteppedFlapjack.StackRemoveSteps.CompCorrect
