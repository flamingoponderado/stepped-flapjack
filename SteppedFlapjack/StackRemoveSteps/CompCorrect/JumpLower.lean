import SteppedFlapjack.StackRemoveSteps.CompCorrect.Loop
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.JumpLower

/-! The `jumpLower` case of the step-counted `stack_remove` correctness theorem
(stepped-flapjack#2, phase C3).

`jumpLower` compiles to itself and runs a program taken from the *code*, not a
structural subterm. Its step bound therefore needs a bound on the code's leaf
costs, which is the program-dependent factor's other half:

`codeBound : forall label program, sptLookup label source.code = some program ->
  leafCost B bounds program <= K`

`K` is chosen per program and discharged when the theorem is applied to a
concrete Pancake source, where the code is known. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectJumpLowerWithinSteps (first second label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (K : Nat) (Kpos : 1 ≤ K)
    (codeBound : ∀ (label : Nat) (program : HolProg width),
      sptLookup label source.code = some program → leafCost B bounds program ≤ K)
    (calleeIH : ∀ (left right : BitVec width) (program : HolProg width),
      getVar first source = some (.word left) → getVar second source = some (.word right) →
      wordCmpHOL .lower left right = true → sptLookup label source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound program k →
      ∃ clock postTarget,
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k program, {t with clock := clock + t.clock}) ≤
          leafCost B off program * steps (program, decClock source))
    (hypothesis : evaluate (.jumpLower first second label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.jumpLower first second label : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.jumpLower first second label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.jumpLower first second label),
        {target with clock := clock + target.clock}) ≤
        K * steps (.jumpLower first second label, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_jumpLower] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
          have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
          by_cases lower : wordCmpHOL .lower left right = true
          · simp only [lower, if_true, StackSemControl.findCode] at sourceRun
            cases lookup : sptLookup label source.code with
            | none =>
              simp only [lookup] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | some program =>
              simp only [lookup] at sourceRun
              obtain ⟨targetLookup, bodyBound⟩ := FindCode.codeLookup jump bounds pointer label source target program relation lookup
              have programBound : leafCost B bounds program ≤ K := codeBound label program lookup
              by_cases zero : source.clock = 0
              · simp only [zero, if_true] at sourceRun
                rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
                subst result
                subst postSource
                refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
                · simpa only [comp, Nat.zero_add] using
                    (evaluate_jumpLower first second label target).trans (by
                      simp only [getVar, targetFirst, targetSecond, lower, if_true,
                        StackSemControl.findCode, targetLookup, clocks, zero])
                · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
                · have src : steps ((.jumpLower first second label : HolProg width), source) = 1 := by
                    rw [steps_jumpLower]
                    simp only [hFirst, hSecond]
                    rw [if_pos lower]
                    simp only [StackSemControl.findCode, lookup, zero, if_pos, Nat.add_zero]
                  have tgt : steps ((.jumpLower first second label : HolProg width), target) = 1 := by
                    rw [steps_jumpLower]
                    simp only [getVar, targetFirst, targetSecond]
                    rw [if_pos lower]
                    simp only [StackSemControl.findCode, targetLookup, clocks, zero, if_pos, Nat.add_zero]
                  simp only [comp]
                  have hstep : steps ((.jumpLower first second label : HolProg width),
                      {target with clock := 0 + target.clock}) = 1 := by
                    simpa only [Nat.zero_add] using tgt
                  rw [hstep, src, Nat.mul_one]
                  exact Kpos
              · simp only [zero, if_false] at sourceRun
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
                    calleeIH left right program hFirst hSecond lower lookup zero bodyResult middle
                      (decClock target) pointer bounds jump
                      ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
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
                    rw [evaluate_jumpLower]
                    simp only [getVar, targetFirst, targetSecond, StackSemControl.findCode,
                      targetLookup, lower, if_true, nonzero, if_false]
                    rw [clockEq, targetRun]
                    simp [bad]
                  · have nonzero : clock + target.clock ≠ 0 := by omega
                    have clockEq : decClock {target with clock := clock + target.clock} =
                        {decClock target with clock := clock + (decClock target).clock} := by
                      simp only [decClock]
                      congr 1
                      omega
                    have tgt : steps ((.jumpLower first second label : HolProg width),
                        {target with clock := clock + target.clock}) =
                        1 + steps (comp jump bounds pointer program,
                          {decClock target with clock := clock + (decClock target).clock}) := by
                      rw [steps_jumpLower]
                      simp only [getVar, targetFirst, targetSecond]
                      rw [if_pos lower]
                      simp only [StackSemControl.findCode, targetLookup, nonzero, if_false]
                      rw [clockEq]
                    have src : steps ((.jumpLower first second label : HolProg width), source) =
                        1 + steps (program, decClock source) := by
                      rw [steps_jumpLower]
                      simp only [hFirst, hSecond]
                      rw [if_pos lower]
                      simp only [StackSemControl.findCode, lookup, zero, if_false]
                    simp only [comp]
                    rw [tgt, src]
                    calc 1 + steps (comp jump bounds pointer program,
                          {decClock target with clock := clock + (decClock target).clock})
                        ≤ 1 + leafCost B bounds program * steps (program, decClock source) :=
                          Nat.add_le_add_left calleeSteps 1
                      _ ≤ 1 + K * steps (program, decClock source) :=
                          Nat.add_le_add_left (Nat.mul_le_mul_right _ programBound) 1
                      _ ≤ K + K * steps (program, decClock source) :=
                          Nat.add_le_add_right Kpos _
                      _ = K * (1 + steps (program, decClock source)) := by
                          rw [Nat.mul_add, Nat.mul_one]
          · simp [lower] at sourceRun
            rcases sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            refine ⟨0, target, ?_, relation, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                (evaluate_jumpLower first second label target).trans (by
                  simp [getVar, targetFirst, targetSecond, lower])
            · have src : steps ((.jumpLower first second label : HolProg width), source) = 1 := by
                rw [steps_jumpLower]
                simp only [hFirst, hSecond]
                rw [if_neg lower]
              have tgt : steps ((.jumpLower first second label : HolProg width), target) = 1 := by
                rw [steps_jumpLower]
                simp only [getVar, targetFirst, targetSecond]
                rw [if_neg lower]
              simp only [comp]
              have hstep : steps ((.jumpLower first second label : HolProg width),
                  {target with clock := 0 + target.clock}) = 1 := by
                simpa only [Nat.zero_add] using tgt
              rw [hstep, src, Nat.mul_one]
              exact Kpos

end SteppedFlapjack.StackRemoveSteps.CompCorrect
