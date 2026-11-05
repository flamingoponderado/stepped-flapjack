import SteppedFlapjack.StackRemoveSteps.CompCorrect.Statement
import SteppedFlapjack.StackSteps.AddClock
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Seq

/-! Phase C3 of stepped-flapjack#2: the `Seq` case of the step-counted
`stack_remove` correctness induction.

The two induction hypotheses carry the same `leafCost` bound as the conclusion;
the enclosing node's factor is the maximum of the two subprograms' factors
(`leafCost_seq_left`, `leafCost_seq_right`), and every program takes at least one
step (`one_le_leafCost`, `steps_pos`), which pays for the `Seq` node itself.

When the first half runs normally, the induction hands its target run a clock of
`firstClock + target.clock`, while the compiled `Seq` continues at
`firstClock + secondClock + target.clock`. `steps_addClock` is what lets the
first half's bound be reused at the larger clock: the run does not time out, so
its step count is unchanged. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectSeqWithinSteps
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) (B : Nat)
    (firstIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound first k →
      ∃ clock postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k first, {t with clock := clock + t.clock})
          ≤ leafCost B off first * steps (first, source))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (first, source) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k middle t ∧ Flapjack.Compiler.Backend.StackProps.regBound second k →
      ∃ clock postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k second, {t with clock := clock + t.clock})
          ≤ leafCost B off second * steps (second, middle))
    (hypothesis : evaluate (.seq first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.seq first second) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock})
        ≤ leafCost B bounds (.seq first second) * steps (.seq first second, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change Flapjack.Compiler.Backend.StackProps.regBound first pointer ∧ Flapjack.Compiler.Backend.StackProps.regBound second pointer at lower
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
    rw [Compiler.Backend.StackRemove.CompCorrect.Seq.evaluateSeqNone first second source
      middle firstRun] at sourceRun
    obtain ⟨firstClock, middleTarget, firstTargetRun, middleRelation, firstSteps⟩ :=
      firstIH none middle target pointer bounds jump ⟨firstRun, by simp, relation, lower.1⟩
    change stateRelHOL jump bounds pointer middle middleTarget at middleRelation
    obtain ⟨secondClock, postTarget, secondTargetRun, postRelation, secondSteps⟩ :=
      secondIH middle firstRun result postSource middleTarget pointer bounds jump
        ⟨sourceRun, notError, middleRelation, lower.2⟩
    have extraRun := Flapjack.Compiler.Backend.StackProps.evaluateAddClock secondClock
      (comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun :
        evaluate (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
    refine ⟨firstClock + secondClock, postTarget, ?_, ?_, ?_⟩
    · simp only [comp]
      rw [Compiler.Backend.StackRemove.CompCorrect.Seq.evaluateSeqNone _ _ _ _ combinedRun]
      exact secondTargetRun
    · cases result with
      | none => exact postRelation
      | some value => cases value <;> exact postRelation
    · have clockExt : steps (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          steps (comp jump bounds pointer first,
            {target with clock := firstClock + target.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          steps_addClock secondClock _ _ _ rfl none middleTarget firstTargetRun (by simp)
      have seqSteps : steps ((.seq first second : HolProg width), source) =
          1 + steps (first, source) + steps (second, middle) :=
        steps_seq_run first second source middle firstRun
      simp only [comp]
      rw [steps_seq_run _ _ _ _ combinedRun, clockExt, seqSteps]
      have hK1 := leafCost_seq_left B bounds first second
      have hK2 := leafCost_seq_right B bounds first second
      have hKpos := one_le_leafCost B bounds (.seq first second)
      nlinarith [firstSteps, secondSteps, steps_pos first source, steps_pos second middle]
  | some firstResult =>
    rw [Compiler.Backend.StackRemove.CompCorrect.Seq.evaluateSeqSome first second source
      middle firstResult firstRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨clock, postTarget, targetRun, postRelation, targetSteps⟩ :=
      firstIH (some firstResult) middle target pointer bounds jump
        ⟨firstRun, notError, relation, lower.1⟩
    refine ⟨clock, postTarget, ?_, ?_, ?_⟩
    · simp only [comp]
      rw [Compiler.Backend.StackRemove.CompCorrect.Seq.evaluateSeqSome _ _ _ _ _ targetRun]
    · cases firstResult <;> exact postRelation
    · have seqSteps : steps ((.seq first second : HolProg width), source) =
          1 + steps (first, source) := by
        rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, firstRun]
        try dsimp only
        omega
      simp only [comp]
      rw [steps_seq, targetRun]
      try dsimp only
      rw [seqSteps]
      have hK1 := leafCost_seq_left B bounds first second
      have hKpos := one_le_leafCost B bounds (.seq first second)
      have hX : steps (comp jump bounds pointer first, {target with clock := clock + target.clock})
          ≤ leafCost B bounds (.seq first second) * steps (first, source) :=
        le_trans targetSteps (Nat.mul_le_mul_right _ hK1)
      calc 1 + steps (comp jump bounds pointer first, {target with clock := clock + target.clock})
          ≤ leafCost B bounds (.seq first second) + leafCost B bounds (.seq first second) * steps (first, source) := by
            omega
        _ = leafCost B bounds (.seq first second) * (1 + steps (first, source)) := by
            rw [Nat.mul_add, Nat.mul_one]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
