import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Install
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.ShMem
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Ffi

/-! Adapted copy of `Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect.lean`
(stepped-flapjack#2, phase C1). The cases are assembled into `flattenPropAll`
by the same well-founded induction. The original `flattenCorrect` becomes
`flattenCorrectWithin`, whose conclusion has the extra conjunct
`t1.clock + ck ≤ t2.clock + flattenStepFactor * steps (prog, s1)`: the LabSem
run takes at most `flattenStepFactor` ticks per StackSem step.
`flattenCorrect_of_within` recovers the original statement. The `@[hol]`
attribute and the representation witness
`holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact`, which only
serves it, are dropped. Otherwise the proofs follow the original. -/

/-! `flatten_correct` (`stack_to_labProofScript.sml:1207-2740`): the HOL proof
is by `evaluate_ind`; here the constructor cases of `FlattenCorrect/` are
assembled by well-founded induction on the evaluator's `(clock, size)`
measure, which covers every recursive call of `evaluate_ind`. -/

namespace SteppedFlapjack.StackToLabSteps
open Flapjack hiding flattenHOL
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
  (FlattenHyps FlattenConcl MeasureLt appListAppendList appListAppendAppend)
open SteppedFlapjack.StackSteps

/-- `MeasureLt` is well founded: it is included in the lexicographic order of
`(clock, size)`. -/
theorem measureLtWf {width : Nat} [NeZero width] {C F : Type} :
    WellFounded (fun a b : HolProg width × StackSemStateFiniteExact width C F =>
      MeasureLt a.1 a.2 b.1 b.2) := by
  refine Subrelation.wf (r := InvImage (Prod.Lex (· < ·) (· < ·))
    (fun a : HolProg width × StackSemStateFiniteExact width C F => (a.2.clock, sizeOf a.1)))
    (fun {a b} h => ?_) (InvImage.wf _ (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)
  simp only [InvImage, Prod.lex_def]
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, h2⟩

/-- Every constructor case, given the induction hypothesis. -/
theorem flattenPropOfIH {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F)
    (ih : FlattenIHWithin prog s1) : FlattenPropWithin prog s1 := by
  cases prog with
  | skip => exact flattenCorrectSkip s1
  | inst i => exact flattenCorrectInst s1 i
  | get v name => exact flattenCorrectGet s1 v name
  | set name v => exact flattenCorrectSet s1 v name
  | opCurrHeap op v src => exact flattenCorrectOpCurrHeap s1 op v src
  | call ret dest handler =>
    rcases ret with _ | ⟨rp, link, l1, l2⟩
    · exact flattenCorrectCallTail s1 dest handler ih
    · exact flattenCorrectCallRet s1 rp link l1 l2 dest handler ih
  | seq c1 c2 => exact flattenCorrectSeq s1 c1 c2 ih
  | ite cmp reg ri c1 c2 => exact flattenCorrectIf s1 cmp reg ri c1 c2 ih
  | loop body => exact flattenCorrectLoop s1 body ih
  | jumpLower r1 r2 dest => exact flattenCorrectJumpLower s1 r1 r2 dest ih
  | alloc k => exact flattenCorrectAlloc s1 k
  | storeConsts a b stub => exact flattenCorrectStoreConsts s1 a b stub
  | raise v => exact flattenCorrectRaise s1 v
  | ret v => exact flattenCorrectRet s1 v
  | «break» k => exact flattenCorrectBreak s1 k
  | «continue» k => exact flattenCorrectContinue s1 k
  | ffi f ptr len ptr2 len2 ret => exact flattenCorrectFfi s1 f ptr len ptr2 len2 ret
  | tick => exact flattenCorrectTick s1
  | locValue reg l1 l2 => exact flattenCorrectLocValue s1 reg l1 l2
  | install ptr len dptr dlen ret => exact flattenCorrectInstall s1 ptr len dptr dlen ret
  | shMemOp op reg addr =>
    rcases addr with ⟨a, w⟩
    exact flattenCorrectShMemOp s1 op reg a w
  | codeBufferWrite r1 r2 => exact flattenCorrectCodeBufferWrite s1 r1 r2
  | dataBufferWrite r1 r2 => exact flattenCorrectDataBufferWrite s1 r1 r2
  | rawCall dest => exact flattenCorrectRawCall s1 dest ih
  | stackAlloc k => exact flattenCorrectStackAlloc s1 k
  | stackFree k => exact flattenCorrectStackFree s1 k
  | stackStore r k => exact flattenCorrectStackStore s1 r k
  | stackStoreAny r rn => exact flattenCorrectStackStoreAny s1 r rn
  | stackLoad r k => exact flattenCorrectStackLoad s1 r k
  | stackLoadAny r rn => exact flattenCorrectStackLoadAny s1 r rn
  | stackGetSize r => exact flattenCorrectStackGetSize s1 r
  | stackSetSize r => exact flattenCorrectStackSetSize s1 r
  | bitmapLoad r v => exact flattenCorrectBitmapLoad s1 r v
  | halt v => exact flattenCorrectHalt s1 v

/-- `flatten_correct` for every program and initial state. -/
theorem flattenPropAll {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) : FlattenPropWithin prog s1 :=
  (measureLtWf.induction (C := fun a => FlattenPropWithin a.1 a.2) (prog, s1)
    fun a ih => flattenPropOfIH a.1 a.2 fun p' s' h => ih (p', s') h :)

/-- HOL `flatten_correct` with the LabSem run bounded: a non-error StackSem
evaluation of `prog` is simulated by LabSem execution of its flattening
installed at `t1.pc` in at most `flattenStepFactor * steps (prog, s1)` ticks. -/
theorem flattenCorrectWithin {width : Nat} [NeZero width] {C F : Type} :
    ∀ (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (t : Bool)
      (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
      (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
      StackSemEvaluate.evaluate (prog, s1) = (r, s2) ∧ r ≠ some .error ∧
      stateRel s1 t1 ∧
      Compiler.Backend.StackProps.callArgs prog t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg
          t1.linkReg ∧
      codeInstalled t1.pc (appListAppend (flattenHOL t prog n l cs bs).1) t1.code ∧
      (∀ k ∈ cs ++ bs ++ [0], (locToPc n k t1.code).isSome) →
      ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      t1.clock + ck ≤ t2.clock + flattenStepFactor * steps (prog, s1) ∧
      match haltView r with
      | some res =>
        evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
      | none =>
        (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
          evaluate { t2 with clock := t2.clock + ck1 }) ∧
        t2.lenReg = t1.lenReg ∧
        t2.ptrReg = t1.ptrReg ∧
        t2.len2Reg = t1.len2Reg ∧
        t2.ptr2Reg = t1.ptr2Reg ∧
        t2.linkReg = t1.linkReg ∧
        t1.code <+: t2.code ∧
        match r.map (fun w => resultView w n cs bs) with
        | none =>
          t2.pc = t1.pc + ((appListAppend (flattenHOL t prog n l cs bs).1).filter
            (fun x => !isLabelHOL x)).length ∧
          stateRel s2 t2
        | some (.vloc n1 n2) =>
          (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
            ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
        | some (.vcont n1 n2) =>
          stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
        | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
        | some .verr => False :=
  fun prog s1 t r s2 n l cs bs t1 h => flattenPropAll prog s1 t r s2 n l cs bs t1 h

/-- The bounded statement implies Flapjack's `flatten_correct`, in the form of
`FlattenHyps` and `FlattenConcl`. -/
theorem flattenCorrect_of_within {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (h : FlattenHyps prog s1 t r s2 n l cs bs t1) : FlattenConcl prog t r s2 n l cs bs t1 :=
  FlattenConclBound.toConcl (flattenCorrectWithin prog s1 t r s2 n l cs bs t1 h)

end SteppedFlapjack.StackToLabSteps
