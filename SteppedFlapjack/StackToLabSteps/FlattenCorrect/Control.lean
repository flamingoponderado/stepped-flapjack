import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Leaves
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock
import Flapjack.Compiler.Backend.Semantics.StackSem.Measure.CallSites

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Control.lean`
(stepped-flapjack#2, phase C1): the composition lemmas and the `Seq` case for
`FlattenPropWithin`. The composition lemmas carry tick bounds:
`flattenConclCompose` adds the bound of the prefix run to the bound of the
following conclusion, and `flattenConclNone` also unpacks the bound. `Seq` runs
no LabSem instruction of its own, so its bound is the sum of the bounds of its
two halves. Otherwise the statements and proofs follow the original. -/

/-! `flatten_correct` control-flow cases `Seq`, `If` and `Loop`
(`stack_to_labProofScript.sml:1321-1460`, `1531-1840`). -/

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

section
variable {width : Nat} [NeZero width] {C F : Type}

/-- The conclusion for a result does not depend on the program, tail flag
or next label. -/
theorem flattenConclSome {B : Nat} {p p' : HolProg width} {t t' : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l l' : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (h : FlattenConclBound B p t (some x) s2 n l cs bs t1) :
    FlattenConclBound B p' t' (some x) s2 n l' cs bs t1 := by
  obtain ⟨ck, t2, hb, h⟩ := h
  refine ⟨ck, t2, hb, ?_⟩
  revert h
  cases haltView (some x) with
  | some res => exact id
  | none =>
    simp only [Option.map_some]
    cases resultView x n cs bs <;> exact id

/-- Composition of a LabSem prefix run reaching `t2` with the conclusion of a
following sub-program started in `t2`. The prefix run uses at most `a` ticks
and the sub-program at most `b`. -/
theorem flattenConclCompose {a b : Nat} {p p' : HolProg width} {t t' : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (hb : t1.clock + ck ≤ t2.clock + a)
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (hlen : t1.pc + ((appListAppend (flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
      t2.pc + ((appListAppend (flattenHOL t' p' n l' cs bs).1).filter
        (fun x => !isLabelHOL x)).length)
    (h : FlattenConclBound b p' t' r s2 n l' cs bs t2) :
    FlattenConclBound (a + b) p t r s2 n l cs bs t1 := by
  obtain ⟨ck', t3, hb', h⟩ := h
  refine ⟨ck + ck', t3, by omega, ?_⟩
  revert h
  cases haltView r with
  | some res =>
    rintro ⟨ev, ffi⟩
    refine ⟨?_, ffi⟩
    rw [← Nat.add_assoc, run ck', ev]
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      cases r.map (fun w => resultView w n cs bs) with
      | none => rintro ⟨hpc, rel⟩; exact ⟨by omega, rel⟩
      | some v => cases v <;> exact id

theorem measureLtOfClockLe {p' p : HolProg width} {s' s : StackSemStateFiniteExact width C F}
    (hc : s'.clock ≤ s.clock) (hs : sizeOf p' < sizeOf p) : MeasureLt p' s' p s := by
  rcases Nat.lt_or_eq_of_le hc with h | h
  · exact .inl h
  · exact .inr ⟨h, hs⟩

/-- Unpacked no-result conclusion of a sub-program. -/
theorem flattenConclNone {B : Nat} {p : HolProg width} {t : Bool} {s2 : StackSemStateFiniteExact
    width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (h : FlattenConclBound B p t none s2 n l cs bs t1) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      t1.clock + ck ≤ t2.clock + B ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      t2.pc = t1.pc + ((appListAppend (flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2 := h

/-- Hypotheses of a sub-program run from an intermediate target state. -/
theorem flattenHypsMid {p : HolProg width} {s : StackSemStateFiniteExact width C F} {t : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (ev : StackSemEvaluate.evaluate (p, s) = (r, s2)) (nerr : r ≠ some .error)
    (rel : stateRel s t2)
    (ca : Compiler.Backend.StackProps.callArgs p t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg
        t1.linkReg)
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (inst : codeInstalled t2.pc (appListAppend (flattenHOL t p n l cs bs).1) t1.code)
    (labs : ∀ k ∈ cs ++ bs ++ [0], (locToPc n k t1.code).isSome) :
    FlattenHyps p s t r s2 n l cs bs t2 := by
  refine ⟨ev, nerr, rel, by rw [e1, e2, e3, e4, e5]; exact ca,
    codeInstalledIsPrefix _ _ _ _ ⟨inst, pre⟩,
    fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre⟩⟩

/-- `Seq` case. -/
theorem flattenCorrectSeq (s1 : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (ih : FlattenIHWithin (.seq c1 c2) s1) : FlattenPropWithin (.seq c1 c2) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  rcases h1 : flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (flattenHOL t (.seq c1 c2) n l cs bs).1 =
      appListAppend xs ++ ((if t then [.label n 1 0] else []) ++ appListAppend ys) := by
    rw [flattenHOL]
    cases t <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst
  have instYs : codeInstalled (t1.pc + ((appListAppend xs).filter
      (fun x => !isLabelHOL x)).length) (appListAppend ys) t1.code := by
    cases t
    · simpa using instRest
    · simp only [if_true, List.singleton_append, codeInstalled_cons, isLabelHOL] at instRest
      exact instRest.2
  have lenFlat : ((appListAppend (flattenHOL t (.seq c1 c2) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length +
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length := by
    rw [hflat]; cases t <;> simp [List.filter_append, isLabelHOL]
  have hsteps := steps_seq c1 c2 s1
  rw [StackSemEvaluateClock.fixClockEvaluate] at hsteps
  rcases e1 : StackSemEvaluate.evaluate (c1, s1) with ⟨r1, s1'⟩
  rw [e1] at ev hsteps
  have lt1 : MeasureLt c1 s1 (.seq c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.seq_first_size_lt c1 c2⟩
  cases r1 with
  | some x =>
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have := ih c1 s1 lt1 false (some x) s1' n l cs bs t1
      ⟨e1, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    refine (flattenConclSome this).mono ?_
    simp only [hsteps, flattenStepFactor]
    omega
  | none =>
    simp only at ev
    have c1h := ih c1 s1 lt1 false none s1' n l cs bs t1
      ⟨e1, by simp, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    obtain ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := flattenConclNone c1h
    rw [h1] at hpc
    have lt2 : MeasureLt c2 s1' (.seq c1 c2) s1 :=
      measureLtOfClockLe (StackSemEvaluateClock.evaluateClock _ _ _ _ e1)
        (StackSemMeasure.seq_second_size_lt c1 c2)
    have c2h := ih c2 s1' lt2 false r s2 n l1 cs bs t2
      (flattenHypsMid ev nerr rel2 ca.2 f1 f2 f3 f4 f5 pre
        (by rw [h2, hpc]; exact instYs) labs)
    refine (flattenConclCompose hb run f1 f2 f3 f4 f5 pre ?_ c2h).mono ?_
    · simp only [lenFlat, hpc, h2]
      omega
    · simp only [hsteps, flattenStepFactor]
      omega

end

end SteppedFlapjack.StackToLabSteps
