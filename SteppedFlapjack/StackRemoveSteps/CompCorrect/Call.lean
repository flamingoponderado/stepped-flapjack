import SteppedFlapjack.StackRemoveSteps.CompCorrect.CallReturnHandler

/-! The `call` assembly for the step-counted `stack_remove` correctness theorem
(stepped-flapjack#2, phase C3).

Dispatches on the `ret`/`handler` shapes to `CallTail`, `CallReturnNone` and
`CallReturnHandler`, carrying the code bound, the structural case bound and the
program-dependent factor `K`. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

theorem compCorrectCallWithinSteps
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (_bitmap : bitmapBound (width := width) (C := C) (F := F) B)
    (K : Nat) (Kpos : 1 ≤ K)
    (caseBound : leafCost B bounds (.call ret dest handler) ≤ K)
    (calleeIH : match ret with
      | none =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest source.regs source.code = some program →
            handler = none → source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
                    evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL jump bounds pointer (decClock source) t ∧
              Flapjack.Compiler.Backend.StackProps.regBound program pointer →
            ∃ clock postTarget,
        evaluate (comp jump bounds pointer program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL jump bounds pointer post postTarget) ∧
              steps (comp jump bounds pointer program, {t with clock := clock + t.clock}) ≤
                K * steps (program, decClock source)
      | some (_body, link, l1, l2) =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
                    evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL jump bounds pointer (decClock (setVar link (.loc l1 l2) source)) t ∧
              Flapjack.Compiler.Backend.StackProps.regBound program pointer →
            ∃ clock postTarget,
        evaluate (comp jump bounds pointer program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL jump bounds pointer post postTarget) ∧
              steps (comp jump bounds pointer program, {t with clock := clock + t.clock}) ≤
                K * steps (program, decClock (setVar link (.loc l1 l2) source)))
    (returnIH : match ret with
      | none => True
      | some (body, link, l1, l2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.result (.loc l1 l2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
                    evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL jump bounds pointer (middle) t ∧ Flapjack.Compiler.Backend.StackProps.regBound body pointer →
            ∃ clock postTarget,
        evaluate (comp jump bounds pointer body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL jump bounds pointer post postTarget) ∧
              steps (comp jump bounds pointer body, {t with clock := clock + t.clock}) ≤
                K * steps (body, middle))
    (handlerIH : match ret, handler with
      | some (_body, link, l1, l2), some (handler, hl1, hl2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.exception (.loc hl1 hl2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F),
                    evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL jump bounds pointer (middle) t ∧ Flapjack.Compiler.Backend.StackProps.regBound handler pointer →
            ∃ clock postTarget,
        evaluate (comp jump bounds pointer handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL jump bounds pointer post postTarget) ∧
              steps (comp jump bounds pointer handler, {t with clock := clock + t.clock}) ≤
                K * steps (handler, middle)
      | _, _ => True)
    (hypothesis : evaluate (.call ret dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.call ret dest handler : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.call ret dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.call ret dest handler),
        {target with clock := clock + target.clock}) ≤
        K * steps (.call ret dest handler, source) := by
  cases ret with
  | none =>
    obtain ⟨clock, postTarget, run, relation, stepsBound⟩ :=
      compCorrectCallTailWithinSteps dest handler source result postSource target
        pointer bounds jump B _bitmap K Kpos calleeIH hypothesis
    refine ⟨clock, postTarget, run, ?_, stepsBound⟩
    cases result with
    | none => exact relation
    | some value => cases value <;> exact relation
  | some returning =>
    rcases returning with ⟨body, link, l1, l2⟩
    cases handler with
    | none =>
      obtain ⟨clock, postTarget, run, relation, stepsBound⟩ :=
        compCorrectCallReturnNoneWithinSteps body link l1 l2 dest source result
          postSource target pointer bounds jump B _bitmap K Kpos caseBound
          calleeIH returnIH hypothesis
      refine ⟨clock, postTarget, run, ?_, stepsBound⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation
    | some exceptional =>
      rcases exceptional with ⟨handlerBody, hl1, hl2⟩
      obtain ⟨clock, postTarget, run, relation, stepsBound⟩ :=
        compCorrectCallReturnHandlerWithinSteps body handlerBody link l1 l2 hl1 hl2
          dest source result postSource target pointer bounds jump B _bitmap K Kpos
          caseBound calleeIH returnIH handlerIH hypothesis
      refine ⟨clock, postTarget, run, ?_, stepsBound⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation

end SteppedFlapjack.StackRemoveSteps.CompCorrect
