import SteppedFlapjack.StackRemoveSteps.CompCorrect.RawCall
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail

/-! The `ret = none` `call` case of the step-counted `stack_remove` correctness
theorem (stepped-flapjack#2, phase C3).

The callee is taken from the code through `findCode`; the step bound takes the
callee's bound as an induction hypothesis with the program-dependent factor
`K`. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectCallTailWithinSteps (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (K : Nat) (Kpos : 1 ≤ K)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some program →
      handler = none → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
        evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL jump bounds pointer (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound program pointer →
      ∃ clock postTarget,
        evaluate (comp jump bounds pointer program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL jump bounds pointer post postTarget) ∧
        steps (comp jump bounds pointer program, {t with clock := clock + t.clock}) ≤
          K * steps (program, decClock source))
    (hypothesis : evaluate (.call none dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.call none dest handler : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.call none dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.call none dest handler),
        {target with clock := clock + target.clock}) ≤
        K * steps (.call none dest handler, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_call] at sourceRun
  cases lookup : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases handler with
    | some h =>
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | none =>
      obtain ⟨targetLookup, bodyBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target dest program ⟨relation, by
          simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
          cases dest <;> exact bound.1, lookup⟩
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_call none dest none target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
        · have src : steps ((.call none dest none : HolProg width), source) = 1 := by
            rw [steps_call_none]
            simp only [lookup, zero, if_pos, Nat.add_zero]
          have tgt : steps ((.call none dest none : HolProg width), target) = 1 := by
            rw [steps_call_none]
            simp only [targetLookup, clocks, zero, if_pos, Nat.add_zero]
          simp only [comp]
          have hstep : steps ((.call none dest none : HolProg width),
              {target with clock := 0 + target.clock}) = 1 := by
            simpa only [Nat.zero_add] using tgt
          rw [hstep, src, Nat.mul_one]
          exact Kpos
      · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at sourceRun
        rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeSteps⟩ :=
            calleeIH program lookup rfl zero bodyResult middle (decClock target) ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
          refine ⟨clock, postTarget, ?_, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have clockEq : decClock {target with clock := clock + target.clock} =
                {decClock target with clock := clock + (decClock target).clock} := by
              simp only [decClock]
              congr 1
              omega
            simp only [comp]
            rw [evaluate_call]
            simp only [targetLookup, nonzero, if_false, StackSemEvaluateClock.fixClockEvaluate]
            rw [clockEq, targetRun]
            simp [bad]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have clockEq : decClock {target with clock := clock + target.clock} =
                {decClock target with clock := clock + (decClock target).clock} := by
              simp only [decClock]
              congr 1
              omega
            have tgt : steps ((.call none dest none : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer program,
                  {decClock target with clock := clock + (decClock target).clock}) := by
              rw [steps_call_none]
              simp only [targetLookup, nonzero, if_false]
              rw [clockEq]
            have src : steps ((.call none dest none : HolProg width), source) =
                1 + steps (program, decClock source) := by
              rw [steps_call_none]
              simp only [lookup, zero, if_false]
            simp only [comp]
            rw [tgt, src]
            calc 1 + steps (comp jump bounds pointer program,
                  {decClock target with clock := clock + (decClock target).clock})
                ≤ K + steps (comp jump bounds pointer program,
                    {decClock target with clock := clock + (decClock target).clock}) :=
                  Nat.add_le_add_right Kpos _
              _ ≤ K + K * steps (program, decClock source) :=
                  Nat.add_le_add_left calleeSteps K
              _ = K * (1 + steps (program, decClock source)) := by
                  rw [Nat.mul_add, Nat.mul_one]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
