import SteppedFlapjack.StackRemoveSteps.CompCorrect.JumpLower
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.RawCall

/-! The `rawCall` case of the step-counted `stack_remove` correctness theorem
(stepped-flapjack#2, phase C3).

`rawCall` compiles to itself and runs the body of a `seq` taken from the code,
so like `jumpLower` its step bound takes the callee's bound as an induction
hypothesis with the program-dependent factor `K`, discharged for the concrete
Pancake source at use time. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectRawCallWithinSteps (label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (K : Nat) (Kpos : 1 ≤ K)
    (calleeIH : ∀ (frame body : HolProg width),
      sptLookup label source.code = some (.seq frame body) → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
        evaluate (body, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL jump bounds pointer (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound body pointer →
      ∃ clock postTarget,
        evaluate (comp jump bounds pointer body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL jump bounds pointer post postTarget) ∧
        steps (comp jump bounds pointer body, {t with clock := clock + t.clock}) ≤
          K * steps (body, decClock source))
    (hypothesis : evaluate (.rawCall label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.rawCall label : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.rawCall label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.rawCall label),
        {target with clock := clock + target.clock}) ≤
        K * steps (.rawCall label, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_rawCall] at sourceRun
  cases lookup : sptLookup label source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases shape : StackSemControl.destSeq program with
    | none =>
      simp only [shape] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | some pair =>
      rcases pair with ⟨frame, body⟩
      have programEq : program = .seq frame body := by
        cases program <;> simp [StackSemControl.destSeq] at shape ⊢
        exact ⟨shape.1, shape.2⟩
      subst program
      simp only [StackSemControl.destSeq] at sourceRun
      obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target (.inl label) (.seq frame body) ⟨relation, True.intro, lookup⟩
      change sptLookup label target.code = some (comp jump bounds pointer (.seq frame body)) at targetLookup
      simp only [comp] at targetLookup
      change Flapjack.Compiler.Backend.StackProps.regBound frame pointer ∧
        Flapjack.Compiler.Backend.StackProps.regBound body pointer at programBound
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_rawCall label target).trans (by
              simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
        · have src : steps ((.rawCall label : HolProg width), source) = 1 := by
            rw [steps_rawCall]
            simp only [lookup, StackSemControl.destSeq, zero, if_pos, Nat.add_zero]
          have tgt : steps ((.rawCall label : HolProg width), target) = 1 := by
            rw [steps_rawCall]
            simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_pos, Nat.add_zero]
          simp only [comp]
          have hstep : steps ((.rawCall label : HolProg width),
              {target with clock := 0 + target.clock}) = 1 := by
            simpa only [Nat.zero_add] using tgt
          rw [hstep, src, Nat.mul_one]
          exact Kpos
      · simp only [zero, if_false] at sourceRun
        rcases bodyRun : evaluate (body, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeSteps⟩ :=
            calleeIH frame body lookup zero bodyResult middle (decClock target) ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, programBound.2⟩
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
            rw [evaluate_rawCall]
            simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
            rw [clockEq, targetRun]
            simp [bad]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have clockEq : decClock {target with clock := clock + target.clock} =
                {decClock target with clock := clock + (decClock target).clock} := by
              simp only [decClock]
              congr 1
              omega
            have tgt : steps ((.rawCall label : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer body,
                  {decClock target with clock := clock + (decClock target).clock}) := by
              rw [steps_rawCall]
              simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
              rw [clockEq]
            have src : steps ((.rawCall label : HolProg width), source) =
                1 + steps (body, decClock source) := by
              rw [steps_rawCall]
              simp only [lookup, StackSemControl.destSeq, zero, if_false]
            simp only [comp]
            rw [tgt, src]
            calc 1 + steps (comp jump bounds pointer body,
                  {decClock target with clock := clock + (decClock target).clock})
                ≤ K + steps (comp jump bounds pointer body,
                    {decClock target with clock := clock + (decClock target).clock}) :=
                  Nat.add_le_add_right Kpos _
              _ ≤ K + K * steps (body, decClock source) :=
                  Nat.add_le_add_left calleeSteps K
              _ = K * (1 + steps (body, decClock source)) := by
                  rw [Nat.mul_add, Nat.mul_one]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
