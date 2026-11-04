import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Statement
import SteppedFlapjack.StackToLabSteps.Defs

/-! Adapted copy of `Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Statement.lean`
(stepped-flapjack#2, phase C1). The hypotheses `FlattenHyps` and the measure
`MeasureLt` are Flapjack's, imported from the original; it is the one copy that
imports its original, because the bounded statement is stated against them and
against `FlattenConcl`. `FlattenConclBound B` is `FlattenConcl` with one more
conjunct, `t1.clock + ck ≤ t2.clock + B`: the LabSem run uses at most `B`
ticks. `FlattenConclWithin` takes `B = flattenStepFactor * steps (prog, s1)`,
and `FlattenPropWithin` and `FlattenIHWithin` are `FlattenProp` and
`FlattenIH` with that conclusion. The `Skip` case and `flattenConclStay` are
copied with the bound; `FlattenConclBound.mono` weakens the bound and
`FlattenConclBound.toConcl` forgets it. -/

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

/-- The conclusion of `flatten_correct` with the LabSem run bounded by `B`
ticks: `t1.clock + ck - t2.clock` ticks are used, since the run starts with
`t1.clock + ck` and ends with `t2.clock`. -/
def FlattenConclBound {width : Nat} [NeZero width] {C F : Type} (B : Nat)
    (prog : HolProg width) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    t1.clock + ck ≤ t2.clock + B ∧
    match haltView r with
    | some res => evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
    | none =>
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      match r.map (fun w => resultView w n cs bs) with
      | none =>
        t2.pc = t1.pc + ((appListAppend (flattenHOL t prog n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2
      | some (.vloc n1 n2) =>
        (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
          ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
      | some (.vcont n1 n2) =>
        stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
      | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
      | some .verr => False

/-- The conclusion of `flatten_correct` with the LabSem run bounded by
`flattenStepFactor` ticks per StackSem step of `prog` from `s1`. -/
def FlattenConclWithin {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F) (n l : Nat)
    (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) : Prop :=
  FlattenConclBound (flattenStepFactor * steps (prog, s1)) prog t r s2 n l cs bs t1

/-- The bounded `flatten_correct` for one program and initial state. -/
def FlattenPropWithin {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
    FlattenHyps prog s1 t r s2 n l cs bs t1 → FlattenConclWithin prog s1 t r s2 n l cs bs t1

/-- The induction hypothesis available to a constructor case. -/
def FlattenIHWithin {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (p' : HolProg width) (s' : StackSemStateFiniteExact width C F),
    MeasureLt p' s' p s → FlattenPropWithin p' s'

section
variable {width : Nat} [NeZero width] {C F : Type}

/-- A larger bound. -/
theorem FlattenConclBound.mono {B B' : Nat} {prog : HolProg width} {t : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (h : FlattenConclBound B prog t r s2 n l cs bs t1) (hle : B ≤ B') :
    FlattenConclBound B' prog t r s2 n l cs bs t1 := by
  obtain ⟨ck, t2, hb, h⟩ := h
  exact ⟨ck, t2, by omega, h⟩

/-- Forgetting the bound gives Flapjack's conclusion. -/
theorem FlattenConclBound.toConcl {B : Nat} {prog : HolProg width} {t : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (h : FlattenConclBound B prog t r s2 n l cs bs t1) :
    FlattenConcl prog t r s2 n l cs bs t1 := by
  obtain ⟨ck, t2, -, h⟩ := h
  exact ⟨ck, t2, h⟩

/-- A node without recursive `evaluate` calls is allowed `flattenStepFactor`
ticks. -/
theorem stepFactorLeaf {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    (hp : isRecursive p = false) : flattenStepFactor * steps (p, s) = flattenStepFactor := by
  rw [steps_leaf p s hp, Nat.mul_one]

/-- The tick bound of a leaf: at most `flattenStepFactor` ticks. -/
theorem leafBound {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    (hp : isRecursive p = false) {a b : Nat} (h : a ≤ b + flattenStepFactor) :
    a ≤ b + flattenStepFactor * steps (p, s) := by
  rw [stepFactorLeaf hp]; exact h

/-- Every node is allowed at least `flattenStepFactor` ticks. -/
theorem oneStepBound {p : HolProg width} {s : StackSemStateFiniteExact width C F}
    {a b : Nat} (h : a ≤ b + flattenStepFactor) :
    a ≤ b + flattenStepFactor * steps (p, s) :=
  Nat.le_trans h (Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (steps_pos p s)) b)

/-- A program whose flattening is empty and that leaves the state unchanged
without a result is simulated by staying put. -/
theorem flattenConclStay {B : Nat} {prog : HolProg width}
    {t : Bool} {s : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (rel : stateRel s t1)
    (empty : ((appListAppend (flattenHOL t prog n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 0) :
    FlattenConclBound B prog t none s n l cs bs t1 := by
  refine ⟨0, t1, by omega, ?_⟩
  simp only [haltView, Option.map_none, true_and]
  exact ⟨fun ck1 => by simp, List.prefix_refl _, by omega, rel⟩

/-- `Skip` case. -/
theorem flattenCorrectSkip (s1 : StackSemStateFiniteExact width C F) :
    FlattenPropWithin (.skip : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, -, -⟩
  rw [StackSemEvaluate.evaluate_skip] at ev
  cases ev
  exact flattenConclStay rel (by simp [flattenHOL, (appListAppend_thm .nil .nil []).2.1])

end

end SteppedFlapjack.StackToLabSteps
