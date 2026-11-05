import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnNone
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnHandler

/-! The returning `call` with an exception handler, for the step-counted
`stack_remove` correctness theorem (stepped-flapjack#2, phase C3).

Same shape as `CallReturnNone`, with an extra successful-exception branch that
runs the handler body instead of the return continuation. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectCallReturnHandlerWithinSteps (body handler : HolProg width)
    (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (K : Nat) (Kpos : 1 ≤ K)
    (caseBound : leafCost B bounds
      (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))) ≤ K)
    (codeBound : ∀ (label : Nat) (program : HolProg width),
      sptLookup label source.code = some program → leafCost B bounds program ≤ K)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧
        Flapjack.Compiler.Backend.StackProps.regBound program k →
      ∃ clock postTarget,
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k program, {t with clock := clock + t.clock}) ≤
          leafCost B off program * steps (program, decClock (setVar link (.loc l1 l2) source)))
    (returnIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.result (.loc l1 l2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ Flapjack.Compiler.Backend.StackProps.regBound body k →
      ∃ clock postTarget,
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k body, {t with clock := clock + t.clock}) ≤
          leafCost B off body * steps (body, middle))
    (handlerIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ Flapjack.Compiler.Backend.StackProps.regBound handler k →
      ∃ clock postTarget,
        evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k handler, {t with clock := clock + t.clock}) ≤
          leafCost B off handler * steps (handler, middle))
    (hypothesis : evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
        (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound
        (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))),
        {target with clock := clock + target.clock}) ≤
        K * steps (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerUnclamped] at sourceRun
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    obtain ⟨label, spt⟩ := findCode_sptLookup lookup
    have programCostBound : leafCost B bounds program ≤ K := codeBound label program spt
    obtain ⟨targetLookup, programRegBound⟩ := FindCode.findCodeLemmaErased jump bounds pointer
      source target dest program link ⟨relation, by
        simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
        cases dest <;> exact bound.1, lookup⟩
    have bodyBound : Flapjack.Compiler.Backend.StackProps.regBound body pointer := by
      simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
      exact bound.2.1
    have linkBound : link < pointer := by
      simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
      exact bound.2.2.1
    have handlerBound : Flapjack.Compiler.Backend.StackProps.regBound handler pointer := by
      simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
      exact bound.2.2.2
    have bodyCostBound : leafCost B bounds body ≤ K :=
      le_trans (callLeafCostReturn B bounds body link l1 l2 dest (some (handler, hl1, hl2))) caseBound
    have handlerCostBound : leafCost B bounds handler ≤ K :=
      le_trans (callLeafCostHandler B bounds (some (body, link, l1, l2)) dest handler hl1 hl2) caseBound
    by_cases zero : source.clock = 0
    · simp only [zero, if_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerUnclamped
            (comp jump bounds pointer body) (comp jump bounds pointer handler)
            link l1 l2 hl1 hl2 dest target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
            source) = 1 := by
          rw [steps_call_some]
          simp only [lookup, zero, if_pos, Nat.add_zero]
        have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
            (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width), target) = 1 := by
          rw [steps_call_some]
          simp only [targetLookup, clocks, zero, if_pos, Nat.add_zero]
        simp only [comp]
        have hstep : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
            (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
            {target with clock := 0 + target.clock}) = 1 := by
          simpa only [Nat.zero_add] using tgt
        rw [hstep, src, Nat.mul_one]
        exact Kpos
    · simp only [zero, if_false] at sourceRun
      have targetNonzero : target.clock ≠ 0 := by omega
      have entry := Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryRelation
        jump bounds pointer link l1 l2 source target relation linkBound
      rcases bodyRun : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
        ⟨bodyResult, middle⟩
      rw [bodyRun] at sourceRun
      cases bodyResult with
      | none =>
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | error => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «break» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «continue» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | result value =>
          change (if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc l1 l2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, calleeRun, middleRelation, calleeSteps⟩ :=
              calleeIH program lookup zero (some (.result (.loc l1 l2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programRegBound⟩
            obtain ⟨second, postTarget, returnRun, postRelation, returnSteps⟩ :=
              returnIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, bodyBound⟩
            have boosted := Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.calleeAllowance
              (comp jump bounds pointer program) target middleTarget
              link l1 l2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, ?_, ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerResult
                (comp jump bounds pointer body) (comp jump bounds pointer handler)
                (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
            · have calleeAt : steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) =
                  steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  steps_addClock second _ _ _ rfl (some (.result (.loc l1 l2))) middleTarget
                    calleeRun (by simp)
              have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
                  (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
                  {target with clock := (first + second) + target.clock}) =
                  1 + steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                    steps (comp jump bounds pointer body,
                      {middleTarget with clock := second + middleTarget.clock}) := by
                have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
                rw [steps_call_some]
                simp only [targetLookup, totalNonzero, if_false]
                rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                  target link l1 l2 (first + second) targetNonzero]
                rw [StackSemEvaluateClock.fixClockEvaluate]
                have boosted' : evaluate (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) =
                    (some (.result (.loc l1 l2)), {middleTarget with clock := second + middleTarget.clock}) := by
                  rw [← Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                    target link l1 l2 (first + second) targetNonzero]
                  exact boosted
                rw [boosted']
                simp only []
                rw [if_pos trivial]
                ring
              have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
                  source) =
                  1 + steps (program, decClock (setVar link (.loc l1 l2) source)) + steps (body, middle) := by
                rw [steps_call_some]
                simp only [lookup, zero, if_false]
                rw [StackSemEvaluateClock.fixClockEvaluate]
                rw [bodyRun]
                simp only []
                rw [if_pos trivial]
                ring
              simp only [comp]
              rw [tgt, src, calleeAt]
              calc 1 + steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                    steps (comp jump bounds pointer body,
                      {middleTarget with clock := second + middleTarget.clock})
                  = 1 + (steps (comp jump bounds pointer program,
                      {decClock (setVar link (.loc l1 l2) target) with
                        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                      steps (comp jump bounds pointer body,
                        {middleTarget with clock := second + middleTarget.clock})) := by ring
                _ ≤ 1 + (leafCost B bounds program * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      leafCost B bounds body * steps (body, middle)) :=
                    Nat.add_le_add_left (Nat.add_le_add calleeSteps returnSteps) 1
                _ ≤ 1 + (K * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      K * steps (body, middle)) := by
                    have h1 := Nat.mul_le_mul_right
                      (steps (program, decClock (setVar link (.loc l1 l2) source))) programCostBound
                    have h2 := Nat.mul_le_mul_right (steps (body, middle)) bodyCostBound
                    omega
                _ ≤ K + (K * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      K * steps (body, middle)) := by
                    omega
                _ = K * (1 + steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      steps (body, middle)) := by ring
        | halt n =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeSteps⟩ :=
            calleeIH program lookup zero (some (.halt n)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programRegBound⟩
          refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
          · have nonzero : clock + target.clock ≠ 0 := by omega
            simp only [comp]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerUnclamped]
            simp only [targetLookup, nonzero, if_false]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
              target link l1 l2 clock targetNonzero, targetRun]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
                (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock}) := by
              rw [steps_call_some]
              simp only [targetLookup, nonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                target link l1 l2 clock targetNonzero]
              rw [targetRun]
              simp
            have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
                source) = 1 + steps (program, decClock (setVar link (.loc l1 l2) source)) := by
              rw [steps_call_some]
              simp only [lookup, zero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [bodyRun]
              simp
            simp only [comp]
            rw [tgt, src]
            calc 1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock})
                ≤ 1 + leafCost B bounds program * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left calleeSteps 1
              _ ≤ 1 + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left (Nat.mul_le_mul_right _ programCostBound) 1
              _ ≤ K + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_right Kpos _
              _ = K * (1 + steps (program, decClock (setVar link (.loc l1 l2) source))) := by
                  rw [Nat.mul_add, Nat.mul_one]
        | timeOut =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeSteps⟩ :=
            calleeIH program lookup zero (some (.timeOut)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programRegBound⟩
          refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
          · have nonzero : clock + target.clock ≠ 0 := by omega
            simp only [comp]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerUnclamped]
            simp only [targetLookup, nonzero, if_false]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
              target link l1 l2 clock targetNonzero, targetRun]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
                (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock}) := by
              rw [steps_call_some]
              simp only [targetLookup, nonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                target link l1 l2 clock targetNonzero]
              rw [targetRun]
              simp
            have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
                source) = 1 + steps (program, decClock (setVar link (.loc l1 l2) source)) := by
              rw [steps_call_some]
              simp only [lookup, zero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [bodyRun]
              simp
            simp only [comp]
            rw [tgt, src]
            calc 1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock})
                ≤ 1 + leafCost B bounds program * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left calleeSteps 1
              _ ≤ 1 + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left (Nat.mul_le_mul_right _ programCostBound) 1
              _ ≤ K + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_right Kpos _
              _ = K * (1 + steps (program, decClock (setVar link (.loc l1 l2) source))) := by
                  rw [Nat.mul_add, Nat.mul_one]
        | finalFFI event =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeSteps⟩ :=
            calleeIH program lookup zero (some (.finalFFI event)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programRegBound⟩
          refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
          · have nonzero : clock + target.clock ≠ 0 := by omega
            simp only [comp]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerUnclamped]
            simp only [targetLookup, nonzero, if_false]
            rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
              target link l1 l2 clock targetNonzero, targetRun]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
                (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock}) := by
              rw [steps_call_some]
              simp only [targetLookup, nonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                target link l1 l2 clock targetNonzero]
              rw [targetRun]
              simp
            have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
                source) = 1 + steps (program, decClock (setVar link (.loc l1 l2) source)) := by
              rw [steps_call_some]
              simp only [lookup, zero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              rw [bodyRun]
              simp
            simp only [comp]
            rw [tgt, src]
            calc 1 + steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := clock + (decClock (setVar link (.loc l1 l2) target)).clock})
                ≤ 1 + leafCost B bounds program * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left calleeSteps 1
              _ ≤ 1 + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_left (Nat.mul_le_mul_right _ programCostBound) 1
              _ ≤ K + K * steps (program, decClock (setVar link (.loc l1 l2) source)) :=
                  Nat.add_le_add_right Kpos _
              _ = K * (1 + steps (program, decClock (setVar link (.loc l1 l2) source))) := by
                  rw [Nat.mul_add, Nat.mul_one]
        | exception value =>
          change (if value ≠ .loc hl1 hl2 then (some .error, middle)
            else evaluate (handler, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc hl1 hl2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, calleeRun, middleRelation, calleeSteps⟩ :=
              calleeIH program lookup zero (some (.exception (.loc hl1 hl2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programRegBound⟩
            obtain ⟨second, postTarget, returnRun, postRelation, handlerSteps⟩ :=
              handlerIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, handlerBound⟩
            have boosted := Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.exceptionAllowance
              (comp jump bounds pointer program) target middleTarget
              link l1 l2 hl1 hl2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, ?_, ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler.evaluateCallReturnHandlerException
                (comp jump bounds pointer body) (comp jump bounds pointer handler)
                (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
            · have calleeAt : steps (comp jump bounds pointer program,
                  {decClock (setVar link (.loc l1 l2) target) with
                    clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) =
                  steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) := by
                simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  steps_addClock second _ _ _ rfl (some (.exception (.loc hl1 hl2))) middleTarget
                    calleeRun (by simp)
              have tgt : steps ((.call (some (comp jump bounds pointer body, link, l1, l2)) dest
                  (some (comp jump bounds pointer handler, hl1, hl2)) : HolProg width),
                  {target with clock := (first + second) + target.clock}) =
                  1 + steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                    steps (comp jump bounds pointer handler,
                      {middleTarget with clock := second + middleTarget.clock}) := by
                have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
                rw [steps_call_some]
                simp only [targetLookup, totalNonzero, if_false]
                rw [Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                  target link l1 l2 (first + second) targetNonzero]
                rw [StackSemEvaluateClock.fixClockEvaluate]
                have boosted' : evaluate (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := (first + second) + (decClock (setVar link (.loc l1 l2) target)).clock}) =
                    (some (.exception (.loc hl1 hl2)), {middleTarget with clock := second + middleTarget.clock}) := by
                  rw [← Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone.entryClock
                    target link l1 l2 (first + second) targetNonzero]
                  exact boosted
                rw [boosted']
                simp only []
                rw [if_pos trivial]
                ring
              have src : steps ((.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)) : HolProg width),
                  source) =
                  1 + steps (program, decClock (setVar link (.loc l1 l2) source)) + steps (handler, middle) := by
                rw [steps_call_some]
                simp only [lookup, zero, if_false]
                rw [StackSemEvaluateClock.fixClockEvaluate]
                rw [bodyRun]
                simp only []
                rw [if_pos trivial]
                ring
              simp only [comp]
              rw [tgt, src, calleeAt]
              calc 1 + steps (comp jump bounds pointer program,
                    {decClock (setVar link (.loc l1 l2) target) with
                      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                    steps (comp jump bounds pointer handler,
                      {middleTarget with clock := second + middleTarget.clock})
                  = 1 + (steps (comp jump bounds pointer program,
                      {decClock (setVar link (.loc l1 l2) target) with
                        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) +
                      steps (comp jump bounds pointer handler,
                        {middleTarget with clock := second + middleTarget.clock})) := by ring
                _ ≤ 1 + (leafCost B bounds program * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      leafCost B bounds handler * steps (handler, middle)) :=
                    Nat.add_le_add_left (Nat.add_le_add calleeSteps handlerSteps) 1
                _ ≤ 1 + (K * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      K * steps (handler, middle)) := by
                    have h1 := Nat.mul_le_mul_right
                      (steps (program, decClock (setVar link (.loc l1 l2) source))) programCostBound
                    have h2 := Nat.mul_le_mul_right (steps (handler, middle)) handlerCostBound
                    omega
                _ ≤ K + (K * steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      K * steps (handler, middle)) := by
                    omega
                _ = K * (1 + steps (program, decClock (setVar link (.loc l1 l2) source)) +
                      steps (handler, middle)) := by ring

end SteppedFlapjack.StackRemoveSteps.CompCorrect
