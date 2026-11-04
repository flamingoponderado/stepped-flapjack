import SteppedFlapjack.StackToLabSteps.FlattenCorrect.If

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Loop.lean`
(stepped-flapjack#2, phase C1): the `Loop` case for `FlattenPropWithin`. An
iteration runs the body and then one LabSem instruction of the loop, the back
jump; the next iteration is a separate step of the loop. `loopReentry` and
`flattenConclResult` carry the bound of the body. Otherwise the statements and
proofs follow the original. -/

/-! `flatten_correct` case `Loop` (`stack_to_labProofScript.sml:1741-1880`):
the body runs between the continue label and the back jump; `Continue 0` and
normal completion jump back, `Break 0` exits after the break label, and other
results propagate through `exit_loop` with the outer label stacks. -/

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

/-- The body's continuation reaches the back jump with the state relation. -/
theorem loopReentry {B : Nat} {body : HolProg width} {s1' : StackSemStateFiniteExact width C F}
    {res : Option (StackSemResult width)} {n l l1 : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {xs : AppList (LabLineHOL width)} {nr : Bool}
    (h1 : flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) = (xs, nr, l1))
    (fetchJ : asmFetchAux (t1.pc + ((appListAppend xs).filter (fun x => !isLabelHOL x)).length)
      t1.code = some (.labAsm (.jump (.lab n l)) 0 [] 0))
    (hc : StackSemControl.contLoop res = true)
    (bh : FlattenConclBound B body false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      t1.clock + ck ≤ t2.clock + B ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      stateRel s1' t2 ∧ asmFetchAux t2.pc t2.code = some (.labAsm (.jump (.lab n l)) 0 [] 0) := by
  cases res with
  | none =>
    obtain ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := flattenConclNone bh
    rw [h1] at hpc
    exact ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, rel2, by
      rw [hpc]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre⟩⟩
  | some x =>
    rcases x with _ | _ | _ | k | _ | _ | _ | _
    case «continue» =>
      simp only [StackSemControl.contLoop, decide_eq_true_eq] at hc
      subst hc
      obtain ⟨ck, t2, hb, h⟩ := bh
      simp only [haltView, Option.map_some, resultView, findLabHOL,
        List.getElem?_cons_zero, Option.getD_some] at h
      obtain ⟨run, f1, f2, f3, f4, f5, pre, rel2, inst2⟩ := h
      exact ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, rel2, fetchSingle rfl inst2⟩
    all_goals simp [StackSemControl.contLoop] at hc

/-- Results with the same halt view and result view have the same
conclusion, for any program, label stacks and next label. -/
theorem flattenConclResult {B : Nat} {p p' : HolProg width} {t t' : Bool} {x y : StackSemResult
    width}
    {s2 : StackSemStateFiniteExact width C F} {n n' l l' : Nat} {cs bs cs' bs' : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (hh : haltView (some x) = haltView (some y))
    (hr : resultView x n cs bs = resultView y n' cs' bs')
    (h : FlattenConclBound B p t (some x) s2 n l cs bs t1) :
    FlattenConclBound B p' t' (some y) s2 n' l' cs' bs' t1 := by
  obtain ⟨ck, t2, hb, h⟩ := h
  refine ⟨ck, t2, hb, ?_⟩
  revert h
  rw [hh]
  cases haltView (some y) with
  | some res => exact id
  | none =>
    simp only [Option.map_some, hr]
    cases resultView y n' cs' bs' <;> exact id

/-- `Loop` case. -/
theorem flattenCorrectLoop (s1 : StackSemStateFiniteExact width C F) (body : HolProg width)
    (ih : FlattenIHWithin (.loop body) s1) : FlattenPropWithin (.loop body) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  have tf : flattenHOL t (.loop body) n l cs bs = flattenHOL false (.loop body) n l cs bs := by
    cases t
    · rfl
    · exact flattenTF (by simp [isSeqHOL])
  rcases h1 : flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) with ⟨xs, nr1, l1⟩
  have hflat : appListAppend (flattenHOL t (.loop body) n l cs bs).1 =
      .label n l 0 :: (appListAppend xs ++
        [.labAsm (.jump (.lab n l)) 0 [] 0, .label n (l + 1) 0]) := by
    rw [tf, flattenHOL]; simp [h1, appListAppendAppend, appListAppendList]
  have total : ((appListAppend (flattenHOL t (.loop body) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 := by
    rw [hflat]; simp [List.filter_append, isLabelHOL]
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨locL, inst1⟩ := labelAt inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst1
  obtain ⟨fetchJ, instRest2⟩ := lineAt rfl instRest
  obtain ⟨locL1, -⟩ := labelAt instRest2
  have hsteps := steps_loop body s1
  rw [StackSemEvaluateClock.fixClockEvaluate] at hsteps
  rcases e1 : StackSemEvaluate.evaluate (body, s1) with ⟨res, s1'⟩
  rw [e1] at ev hsteps
  simp only at ev hsteps
  have hbody : flattenStepFactor * steps (body, s1) ≤
      flattenStepFactor * steps (.loop body, s1) := by
    rw [hsteps]; simp only [flattenStepFactor]; omega
  have lt1 : MeasureLt body s1 (.loop body) s1 :=
    .inr ⟨rfl, StackSemMeasure.loop_body_size_lt body⟩
  have labs' : ∀ k ∈ (l :: cs) ++ ((l + 1) :: bs) ++ [0], (locToPc n k t1.code).isSome := by
    intro k hk
    by_cases e : k = l
    · subst e; simp [locL]
    by_cases e' : k = l + 1
    · subst e'; simp [locL1]
    apply labs k
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
    tauto
  have nerrBody : res ≠ some .error := by
    rintro rfl
    simp [StackSemControl.contLoop, StackSemControl.exitLoop] at ev
    exact nerr ev.1.symm
  have bh := ih body s1 lt1 false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1
    ⟨e1, nerrBody, rel, ca, by rw [h1]; exact instXs, labs'⟩
  by_cases hc : StackSemControl.contLoop res = true
  · rw [if_pos hc] at ev
    obtain ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, rel2, fetch2⟩ := loopReentry h1 fetchJ hc bh
    split_ifs at ev with hz
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨ck, t2, by omega, run, f1, f2, f3, f4, f5, pre, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel2]
      · rw [relClock rel2]; exact hz
    · have clk2 : t2.clock ≠ 0 := by rw [relClock rel2]; exact hz
      have lt2 : MeasureLt (.loop body) (StackSemStateOps.decClock s1') (.loop body) s1 := by
        left
        have := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
        simp only [StackSemStateOps.decClock]
        omega
      have locL2 := locToPcIsPrefix _ _ _ _ _ ⟨locL, pre⟩
      have rel3 : stateRel (StackSemStateOps.decClock s1')
          { t2 with pc := t1.pc, clock := t2.clock - 1 } := StateRel.stateRelDecClock rel2
      have lh := ih (.loop body) (StackSemStateOps.decClock s1') lt2 t r s2 n l cs bs
        { t2 with pc := t1.pc, clock := t2.clock - 1 }
        ⟨ev, nerr, rel3, by rw [f1, f2, f3, f4, f5]; exact ca,
          codeInstalledIsPrefix _ _ _ _ ⟨inst0, pre⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre⟩⟩
      refine (flattenConclCompose (ck := ck) (t2 := { t2 with pc := t1.pc, clock := t2.clock - 1 })
        (a := flattenStepFactor * steps (body, s1) + 1) (by simp only; omega)
        (fun ck1 => ?_) f1 f2 f3 f4 f5 pre rfl lh).mono ?_
      swap
      · have hz' : s1'.clock ≠ 0 := hz
        rw [hsteps, if_pos ⟨hc, hz'⟩]
        simp only [flattenStepFactor]
        omega
      rw [run, show t2.clock + ck1 = (t2.clock - 1 + ck1) + 1 by omega,
        jumpStep (t2.clock - 1 + ck1) fetch2 locL2]
  · rw [if_neg hc] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine FlattenConclBound.mono (B := flattenStepFactor * steps (body, s1)) ?_ hbody
    rcases res with _ | x
    · simp [StackSemControl.contLoop] at hc
    rcases x with v | v | k | k | v | _ | o | _
    · exact flattenConclResult (h := bh) rfl (by cases v <;> rfl)
    · exact flattenConclResult (h := bh) rfl (by cases v <;> rfl)
    · -- `Break k`
      rcases k with _ | k
      · -- `Break 0` leaves the loop after the break label
        simp only [StackSemControl.exitLoop, if_true]
        obtain ⟨ck, t2, hb, h⟩ := bh
        simp only [haltView, Option.map_some, resultView, findLabHOL,
          List.getElem?_cons_zero, Option.getD_some] at h
        obtain ⟨run, f1, f2, f3, f4, f5, pre, -, hw⟩ := h
        obtain ⟨hpc, rel2⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locL1, pre⟩)
        refine ⟨ck, t2, hb, run, f1, f2, f3, f4, f5, pre, ?_, rel2⟩
        rw [← hpc, total]
        omega
      · simp only [StackSemControl.exitLoop, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        refine flattenConclResult (h := bh) (by simp [haltView]) ?_
        simp [resultView, findLabHOL]
    · -- `Continue k`, `k ≠ 0`
      rcases k with _ | k
      · simp [StackSemControl.contLoop] at hc
      · simp only [StackSemControl.exitLoop, Nat.add_sub_cancel]
        refine flattenConclResult (h := bh) (by simp [haltView]) ?_
        simp [resultView, findLabHOL]
    all_goals exact flattenConclResult (h := bh) rfl (by simp [resultView])

end

end SteppedFlapjack.StackToLabSteps
