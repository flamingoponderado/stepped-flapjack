import SteppedFlapjack.StackRemoveSteps.CompCorrect.Seq
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.If

/-! The `ite` case of the step-counted `stack_remove` correctness theorem
(stepped-flapjack#2, phase C3).

Mirrors Flapjack's `compCorrectIf` and adds the conjunct

`steps (comp ... (.ite cmp r ri a b), {t with clock := clock + t.clock}) <=
  leafCost B bounds (.ite cmp r ri a b) * steps (.ite cmp r ri a b, source)`

The compiled `ite` takes one step for itself plus the steps of the branch that
runs, and the source `ite` likewise takes one step plus its branch, so the same
`1 + X <= K + K * s` arithmetic as the `seq` case closes it. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectIteWithinSteps (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (firstIH : ∀ (left right : WordLocW width),
      StackSemStateOps.getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound first k →
      ∃ clock postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k first, {t with clock := clock + t.clock}) ≤
          leafCost B off first * steps (first, source))
    (secondIH : ∀ (left right : WordLocW width),
      StackSemStateOps.getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound second k →
      ∃ clock postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget) ∧
        steps (comp j off k second, {t with clock := clock + t.clock}) ≤
          leafCost B off second * steps (second, source))
    (hypothesis : evaluate (.ite comparison register operand first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.ite comparison register operand first second) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) ≤
        leafCost B bounds (.ite comparison register operand first second) *
          steps (.ite comparison register operand first second, source) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  simp only [Flapjack.Compiler.Backend.StackProps.regBound] at lower
  have leftEq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩
  have rightEq := Flapjack.Compiler.Backend.StackRemove.CompCorrect.If.operandLookup
    jump bounds pointer source target operand relation lower.2.1
  rw [evaluate_ite] at sourceRun
  cases leftLookup : getVar register source with
  | none =>
    rw [leftLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some left =>
    rw [leftLookup] at sourceRun
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [rightLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some right =>
      rw [rightLookup] at sourceRun
      simp only [] at sourceRun
      cases compared : wordSemWordCmp comparison left right with
      | none =>
        rw [compared] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some truth =>
        cases truth with
        | false =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, targetRun, postRelation, targetSteps⟩ :=
            secondIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.2⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, ?_, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
          · have targetIte : steps ((.ite comparison register operand
                (comp jump bounds pointer first) (comp jump bounds pointer second) : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer second, {target with clock := clock + target.clock}) :=
              steps_ite_false comparison register operand _ _
                {target with clock := clock + target.clock} left right targetLeft targetRight compared
            have sourceIte : steps ((.ite comparison register operand first second : HolProg width), source) =
                1 + steps (second, source) :=
              steps_ite_false comparison register operand first second source left right
                leftLookup rightLookup compared
            simp only [comp]
            rw [targetIte, sourceIte]
            have hK1 := leafCost_ite_right B bounds comparison register operand first second
            have hKpos := one_le_leafCost B bounds (.ite comparison register operand first second)
            have hX : steps (comp jump bounds pointer second, {target with clock := clock + target.clock})
                ≤ leafCost B bounds (.ite comparison register operand first second) * steps (second, source) :=
              le_trans targetSteps (Nat.mul_le_mul_right _ hK1)
            calc 1 + steps (comp jump bounds pointer second, {target with clock := clock + target.clock})
                ≤ leafCost B bounds (.ite comparison register operand first second) +
                    leafCost B bounds (.ite comparison register operand first second) * steps (second, source) := by
                  omega
              _ = leafCost B bounds (.ite comparison register operand first second) *
                    (1 + steps (second, source)) := by
                  rw [Nat.mul_add, Nat.mul_one]
        | true =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, targetRun, postRelation, targetSteps⟩ :=
            firstIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.1⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, ?_, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
          · have targetIte : steps ((.ite comparison register operand
                (comp jump bounds pointer first) (comp jump bounds pointer second) : HolProg width),
                {target with clock := clock + target.clock}) =
                1 + steps (comp jump bounds pointer first, {target with clock := clock + target.clock}) :=
              steps_ite_true comparison register operand _ _
                {target with clock := clock + target.clock} left right targetLeft targetRight compared
            have sourceIte : steps ((.ite comparison register operand first second : HolProg width), source) =
                1 + steps (first, source) :=
              steps_ite_true comparison register operand first second source left right
                leftLookup rightLookup compared
            simp only [comp]
            rw [targetIte, sourceIte]
            have hK1 := leafCost_ite_left B bounds comparison register operand first second
            have hKpos := one_le_leafCost B bounds (.ite comparison register operand first second)
            have hX : steps (comp jump bounds pointer first, {target with clock := clock + target.clock})
                ≤ leafCost B bounds (.ite comparison register operand first second) * steps (first, source) :=
              le_trans targetSteps (Nat.mul_le_mul_right _ hK1)
            calc 1 + steps (comp jump bounds pointer first, {target with clock := clock + target.clock})
                ≤ leafCost B bounds (.ite comparison register operand first second) +
                    leafCost B bounds (.ite comparison register operand first second) * steps (first, source) := by
                  omega
              _ = leafCost B bounds (.ite comparison register operand first second) *
                    (1 + steps (first, source)) := by
                  rw [Nat.mul_add, Nat.mul_one]

end SteppedFlapjack.StackRemoveSteps.CompCorrect
