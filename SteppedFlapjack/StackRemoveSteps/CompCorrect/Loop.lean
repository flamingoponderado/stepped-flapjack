import SteppedFlapjack.StackRemoveSteps.CompCorrect.Ite
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Loop

/-! The `loop` case of the step-counted `stack_remove` correctness theorem
(stepped-flapjack#2, phase C3).

Mirrors Flapjack's `compCorrectLoop` and adds the conjunct

`steps (comp ... (.loop body), {t with clock := clock + t.clock}) <=
  leafCost B bounds (.loop body) * steps (.loop body, source)`

The source and target loops each take one step per iteration plus the body's
steps, so the bound follows the same induction Flapjack's correctness proof
does: the exit branch has `1 + X <= K * (1 + s)`, and the reentry branch has
`1 + X + T' <= K * (1 + s + S')` from the body and reentry induction
hypotheses. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectLoopWithinSteps (body : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (_B : Nat)
    (K : Nat) (Kpos : 1 ≤ K)
    (bodyIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL jump bounds pointer source t ∧ Flapjack.Compiler.Backend.StackProps.regBound body pointer →
      ∃ clock postTarget,
        evaluate (comp jump bounds pointer body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL jump bounds pointer post postTarget) ∧
        steps (comp jump bounds pointer body, {t with clock := clock + t.clock}) ≤
          K * steps (body, source))
    (reentryIH : ∀ (bodyResult : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (bodyResult, middle) →
      StackSemControl.contLoop bodyResult = true → middle.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
        evaluate (.loop body, decClock middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL jump bounds pointer (decClock middle) t ∧
        Flapjack.Compiler.Backend.StackProps.regBound (.loop body) pointer →
      ∃ clock postTarget,
        evaluate (comp jump bounds pointer (.loop body), {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL jump bounds pointer post postTarget) ∧
        steps (comp jump bounds pointer (.loop body), {t with clock := clock + t.clock}) ≤
          K * steps (.loop body, decClock middle))
    (hypothesis : evaluate (.loop body, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.loop body) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.loop body),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.loop body),
        {target with clock := clock + target.clock}) ≤
        K * steps (.loop body, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  rcases bodyRun : evaluate (body, source) with ⟨bodyResult, middle⟩
  have bodyNotError := Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.loopBodyNotError
    body source middle postSource bodyResult result bodyRun sourceRun notError
  obtain ⟨firstClock, middleTarget, firstTargetRun, bodyPost, bodySteps⟩ :=
    bodyIH bodyResult middle target ⟨bodyRun, bodyNotError, relation, by simpa only [Flapjack.Compiler.Backend.StackProps.regBound] using lower⟩
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · have middleRelation : stateRelHOL jump bounds pointer middle middleTarget := by
      rcases Flapjack.Compiler.Backend.StackProps.contLoopImp bodyResult continues with same | same
      · rw [same] at bodyPost; exact bodyPost
      · rw [same] at bodyPost; exact bodyPost
    have middleClocks : middleTarget.clock = middle.clock := middleRelation.2.2.2.2.2.2.2.2.1
    by_cases zero : middle.clock = 0
    · rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopTimeOut
        body source middle bodyResult bodyRun continues zero] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      refine ⟨firstClock, emptyEnv middleTarget, ?_, ?_, ?_⟩
      · simpa only [comp] using
          Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopTimeOut
            (comp jump bounds pointer body)
            {target with clock := firstClock + target.clock} middleTarget bodyResult
            firstTargetRun continues (middleClocks.trans zero)
      · change middleTarget.ffi = middle.ffi
        exact middleRelation.2.2.2.2.2.2.2.2.2.1
      · have targetLoop : steps ((.loop (comp jump bounds pointer body) : HolProg width),
            {target with clock := firstClock + target.clock}) =
            1 + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) :=
          steps_loop_exit (comp jump bounds pointer body) _ middleTarget bodyResult
            firstTargetRun (by rw [middleClocks, zero]; simp)
        have sourceLoop : steps ((.loop body : HolProg width), source) =
            1 + steps (body, source) :=
          steps_loop_exit body source middle bodyResult bodyRun (by simp [continues, zero])
        simp only [comp]
        rw [targetLoop, sourceLoop]
        have hKpos := Kpos
        have hX : steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock})
            ≤ K * steps (body, source) := bodySteps
        calc 1 + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock})
            ≤ K + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) :=
              Nat.add_le_add_right hKpos _
          _ ≤ K + K * steps (body, source) := Nat.add_le_add_left hX K
          _ = K * (1 + steps (body, source)) := by
              rw [Nat.mul_add, Nat.mul_one]
    · rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopReentry
        body source middle bodyResult bodyRun continues zero] at sourceRun
      have decRelation := RelationLaws.stateRelDecClock jump bounds pointer middle middleTarget middleRelation
      obtain ⟨secondClock, postTarget, secondTargetRun, postRelation, reentrySteps⟩ :=
        reentryIH bodyResult middle bodyRun continues zero result postSource
          (decClock middleTarget) ⟨sourceRun, notError, decRelation, lower⟩
      have notTimeout : bodyResult ≠ some .timeOut := by
        rcases Flapjack.Compiler.Backend.StackProps.contLoopImp bodyResult continues with same | same <;> simp [same]
      have extraRun := Flapjack.Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp jump bounds pointer body) {target with clock := firstClock + target.clock}
        bodyResult middleTarget ⟨firstTargetRun, notTimeout⟩
      have combinedRun :
          evaluate (comp jump bounds pointer body,
            {target with clock := (firstClock + secondClock) + target.clock}) =
            (bodyResult, {middleTarget with clock := secondClock + middleTarget.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
      have targetNonzero : middleTarget.clock ≠ 0 := by rw [middleClocks]; exact zero
      have boostedNonzero : ({middleTarget with clock := secondClock + middleTarget.clock}).clock ≠ 0 := by
        change secondClock + middleTarget.clock ≠ 0
        omega
      have decState : decClock {middleTarget with clock := secondClock + middleTarget.clock} =
          {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock} := by
        change {middleTarget with clock := secondClock + middleTarget.clock - 1} =
          {middleTarget with clock := secondClock + (middleTarget.clock - 1)}
        have arithmetic : secondClock + middleTarget.clock - 1 = secondClock + (middleTarget.clock - 1) := by omega
        rw [arithmetic]
      have clockExt : steps (comp jump bounds pointer body,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          steps_addClock secondClock _ _ _ rfl bodyResult middleTarget firstTargetRun notTimeout
      refine ⟨firstClock + secondClock, postTarget, ?_, ?_, ?_⟩
      · rw [comp, Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopReentry
          _ _ _ _ combinedRun continues boostedNonzero, decState]
        simpa only [comp] using secondTargetRun
      · cases result with
        | none => exact postRelation
        | some value => cases value <;> exact postRelation
      · have targetLoop : steps ((.loop (comp jump bounds pointer body) : HolProg width),
            {target with clock := (firstClock + secondClock) + target.clock}) =
            1 + steps (comp jump bounds pointer body,
              {target with clock := (firstClock + secondClock) + target.clock}) +
              steps (.loop (comp jump bounds pointer body),
                decClock {middleTarget with clock := secondClock + middleTarget.clock}) :=
          steps_loop_run (comp jump bounds pointer body) _ _ bodyResult combinedRun continues boostedNonzero
        have sourceLoop : steps ((.loop body : HolProg width), source) =
            1 + steps (body, source) + steps (.loop body, decClock middle) :=
          steps_loop_run body source middle bodyResult bodyRun continues zero
        have reentryAt : steps (.loop (comp jump bounds pointer body),
            decClock {middleTarget with clock := secondClock + middleTarget.clock}) =
            steps (.loop (comp jump bounds pointer body),
              {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock}) := by
          rw [decState]
        simp only [comp]
        rw [targetLoop, sourceLoop, reentryAt, clockExt]
        have hKpos := Kpos
        have hX : steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock})
            ≤ K * steps (body, source) := bodySteps
        have hY : steps (.loop (comp jump bounds pointer body),
            {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock}) ≤
            K * steps (.loop body, decClock middle) := by
          simpa only [comp] using reentrySteps
        calc 1 + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) +
              steps (.loop (comp jump bounds pointer body),
                {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock})
            ≤ K + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) +
                steps (.loop (comp jump bounds pointer body),
                  {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock}) := by
              omega
          _ ≤ K + K * steps (body, source) + K * steps (.loop body, decClock middle) := by
              omega
          _ = K * (1 + steps (body, source) + steps (.loop body, decClock middle)) := by
              ring
  · have exits : StackSemControl.contLoop bodyResult = false := by
      cases equality : StackSemControl.contLoop bodyResult <;> simp_all
    rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopExit
      body source middle bodyResult bodyRun exits] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨firstClock, middleTarget, ?_, ?_, ?_⟩
    · simpa only [comp] using
        Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop.evaluateLoopExit
          (comp jump bounds pointer body)
          {target with clock := firstClock + target.clock} middleTarget bodyResult firstTargetRun exits
    · cases bodyResult with
      | none => simp [StackSemControl.contLoop] at continues
      | some value =>
        cases value with
        | «break» label => cases label <;> exact bodyPost
        | _ => exact bodyPost
    · have targetLoop : steps ((.loop (comp jump bounds pointer body) : HolProg width),
          {target with clock := firstClock + target.clock}) =
          1 + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) :=
        steps_loop_exit (comp jump bounds pointer body) _ middleTarget bodyResult
          firstTargetRun (by simp [exits])
      have sourceLoop : steps ((.loop body : HolProg width), source) =
          1 + steps (body, source) :=
        steps_loop_exit body source middle bodyResult bodyRun (by simp [exits])
      simp only [comp]
      rw [targetLoop, sourceLoop]
      have hKpos := Kpos
      have hX : steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock})
          ≤ K * steps (body, source) := bodySteps
      calc 1 + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock})
          ≤ K + steps (comp jump bounds pointer body, {target with clock := firstClock + target.clock}) :=
            Nat.add_le_add_right hKpos _
        _ ≤ K + K * steps (body, source) := Nat.add_le_add_left hX K
        _ = K * (1 + steps (body, source)) := by
            rw [Nat.mul_add, Nat.mul_one]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
