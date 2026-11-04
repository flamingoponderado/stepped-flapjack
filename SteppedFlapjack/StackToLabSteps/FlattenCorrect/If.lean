import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Control

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/If.lean`
(stepped-flapjack#2, phase C1): the `If` case for `FlattenPropWithin`. The
flattened conditional runs at most two LabSem instructions of its own (the
conditional jump and, in the general shape, the join jump), so the run is
bounded by `2 + flattenStepFactor * steps` of the branch taken.
`flattenConclComposeSome` carries the bounds as `flattenConclCompose` does.
Otherwise the statements and proofs follow the original. -/

/-! `flatten_correct` case `If` (`stack_to_labProofScript.sml:1531-1740`): the
six flattening shapes of a conditional (both branches `Skip`, one `Skip`, a
non-returning branch placed first, or the general shape with a join jump). -/

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

/-- A one-step LabSem transition to a new program counter, run from any
clock, as a prefix run for `flattenConclCompose`. -/
theorem runToPc {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {p : Nat}
    (step : ∀ c, evaluate { t1 with clock := c + 1 } = evaluate { t1 with pc := p, clock := c }) :
    ∀ ck1, evaluate { t1 with clock := t1.clock + 1 + ck1 } =
      evaluate { ({ t1 with pc := p } : Flapjack.Compiler.Backend.LabSem.State width C F) with
        clock := ({ t1 with pc := p } : Flapjack.Compiler.Backend.LabSem.State width C F).clock +
          ck1 } := by
  intro ck1
  rw [show t1.clock + 1 + ck1 = (t1.clock + ck1) + 1 by omega, step]

/-- A fetched conditional jump. -/
theorem jumpCmpStep {t : Flapjack.Compiler.Backend.LabSem.State width C F} {cmp : HolCmp}
    {reg : Nat} {ri : HolRegImm width} {n L : Nat} {b : Bool} (c : Nat)
    (fetch : asmFetchAux t.pc t.code = some (.labAsm (.jumpCmp cmp reg ri (.lab n L)) 0 [] 0))
    (hcmp : wordSemWordCmp cmp (t.regs reg) (regImm ri t) = some b) :
    evaluate { t with clock := c + 1 } =
      if b then
        match locToPc n L t.code with
        | none => (.error, { t with clock := c + 1 })
        | some p => evaluate { t with pc := p, clock := c }
      else evaluate { t with pc := t.pc + 1, clock := c } := by
  rw [evaluate]
  simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch]
  rw [show regImm ri { t with clock := c + 1 } = regImm ri t from
    Compiler.Backend.LabProps.regImmWithClock ri t (c + 1)]
  simp only [hcmp]
  cases b
  · simp [incPc, decClock]
  · simp only [if_true, getPcValue]
    cases locToPc n L t.code <;> simp [updPc, decClock]

/-- A fetched unconditional jump. -/
theorem jumpStep {t : Flapjack.Compiler.Backend.LabSem.State width C F} {n L p : Nat} (c : Nat)
    (fetch : asmFetchAux t.pc t.code = some (.labAsm (.jump (.lab n L)) 0 [] 0))
    (hpc : locToPc n L t.code = some p) :
    evaluate { t with clock := c + 1 } = evaluate { t with pc := p, clock := c } := by
  rw [evaluate]
  simp [asmFetch, fetch, getPcValue, hpc, updPc, decClock]

/-- Composition for a branch that produces a result: the final program
counter is irrelevant. -/
theorem flattenConclComposeSome {a b : Nat} {p p' : HolProg width} {t t' : Bool}
    {x : StackSemResult width} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (hb : t1.clock + ck ≤ t2.clock + a)
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (h : FlattenConclBound b p' t' (some x) s2 n l' cs bs t2) :
    FlattenConclBound (a + b) p t (some x) s2 n l cs bs t1 := by
  obtain ⟨ck', t3, hb', h⟩ := h
  refine ⟨ck + ck', t3, by omega, ?_⟩
  revert h
  cases haltView (some x) with
  | some res =>
    rintro ⟨ev, ffi⟩
    exact ⟨by rw [← Nat.add_assoc, run ck', ev], ffi⟩
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      simp only [Option.map_some]
      cases resultView x n cs bs <;> exact id

theorem isSkipEq {p : HolProg width} (h : stackIsSkip p = true) : p = .skip := by
  cases p <;> simp_all [stackIsSkip]

theorem lineAt {pc : Nat} {x : LabLineHOL width} {rest : List (LabLineHOL width)}
    {code : LabProgHOL width} (nl : isLabelHOL x = false)
    (h : codeInstalled pc (x :: rest) code) :
    asmFetchAux pc code = some x ∧ codeInstalled (pc + 1) rest code := by
  rw [codeInstalled_cons] at h
  simpa [nl] using h

theorem labelAt {pc n L : Nat} {rest : List (LabLineHOL width)} {code : LabProgHOL width}
    (h : codeInstalled pc (.label n L 0 :: rest) code) :
    locToPc n L code = some pc ∧ codeInstalled pc rest code := by
  rw [codeInstalled_cons] at h
  simpa [isLabelHOL] using h

/-- `If` case. -/
theorem flattenCorrectIf (s1 : StackSemStateFiniteExact width C F) (cmp : HolCmp) (reg : Nat)
    (ri : HolRegImm width) (c1 c2 : HolProg width)
    (ih : FlattenIHWithin (.ite cmp reg ri c1 c2) s1) : FlattenPropWithin (.ite cmp reg ri c1 c2)
        s1 := by
  rintro t res s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_ite] at ev
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (res, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  swap; · exact (err ev).elim
  rename_i x y hx hy
  have rx : t1.regs reg = x := InstCorrect.regOfLookup rel hx
  have ry : regImm ri t1 = y := StateRel.stateRelGetVarImm ⟨rel, hy⟩
  rcases hc : wordSemWordCmp cmp x y with _ | b
  · rw [hc] at ev; exact (err ev).elim
  have hcmp : wordSemWordCmp cmp (t1.regs reg) (regImm ri t1) = some b := by rw [rx, ry, hc]
  have hK : flattenStepFactor * steps (.ite cmp reg ri c1 c2, s1) =
      flattenStepFactor + flattenStepFactor * steps (if b then c1 else c2, s1) := by
    rw [steps_ite, hx, hy]
    cases b <;> simp [hc, Nat.mul_add]
  refine FlattenConclBound.mono (B := 2 + flattenStepFactor * steps (if b then c1 else c2, s1)) ?_
    (by rw [hK]; simp only [flattenStepFactor]; omega)
  have hneg : wordSemWordCmp (negateHOL cmp) (t1.regs reg) (regImm ri t1) = some (!b) := by
    rw [Prelude.wordCmpNegate, hcmp]; rfl
  have lt1 : MeasureLt c1 s1 (.ite cmp reg ri c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.if_first_size_lt cmp reg ri c1 c2⟩
  have lt2 : MeasureLt c2 s1 (.ite cmp reg ri c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.if_second_size_lt cmp reg ri c1 c2⟩
  have evb : StackSemEvaluate.evaluate (if b then c1 else c2, s1) = (res, s2) := by
    rw [hc] at ev; cases b <;> exact ev
  rcases h1 : flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have unfold := (show flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs =
      flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs from rfl)
  conv at unfold => rhs; rw [flattenHOL]
  simp only [h1, h2] at unfold
  have nolab : ∀ (a : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString),
      isLabelHOL (Line.labAsm a 0 [] 0 : LabLineHOL width) = false := fun _ => rfl
  have hlenOf : ∀ (L : List (LabLineHOL width)),
      appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 = L →
      ((appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length = (L.filter (fun x => !isLabelHOL x)).length :=
    fun L h => by rw [h]
  split_ifs at unfold with k1 k2 k3 k4 k5
  · -- both branches `Skip`
    simp only [Bool.and_eq_true] at k1
    rw [isSkipEq k1.1, isSkipEq k1.2] at evb
    have : (if b then (.skip : HolProg width) else .skip) = .skip := by cases b <;> rfl
    rw [this, StackSemEvaluate.evaluate_skip] at evb
    simp only [Prod.mk.injEq] at evb
    obtain ⟨rfl, rfl⟩ := evb
    exact flattenConclStay rel (by rw [unfold]; simp [appListAppendList])
  · -- then-branch `Skip`
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · -- condition false: run the else-branch after the fall-through
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      refine (flattenConclCompose (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _) ?_
        (ih c2 s1 lt2 false res s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono
          (by simp)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: jump over the else-branch
      simp only [if_true] at evb
      rw [isSkipEq k2, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine ⟨1, { t1 with pc := t1.pc + 1 + ((appListAppend ys).filter
          (fun x => !isLabelHOL x)).length }, by simp; omega, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- else-branch `Skip`
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · -- condition false: the negated test jumps over the then-branch
      simp only [Bool.false_eq_true, if_false] at evb
      rw [isSkipEq k3, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine ⟨1, { t1 with pc := t1.pc + 1 + ((appListAppend xs).filter
          (fun x => !isLabelHOL x)).length }, by simp; omega, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: fall through into the then-branch
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      refine (flattenConclCompose (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _) ?_
        (ih c1 s1 lt1 false res s2 n l cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono
          (by simp)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- then-branch never returns: placed first
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          (.label n l2 0 :: appListAppend ys)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instYs⟩ := labelAt instLab
    cases b
    · -- condition false: jump to the else-branch
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine (flattenConclCompose (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _) ?_
        (ih c2 s1 lt2 false res s2 n l1 cs bs _
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono
          (by simp)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · -- condition true: the then-branch produces a result
      have some_ := FlattenHelpers.noRetCorrect false c1 n l cs bs (by rw [h1]; exact k4) s1
      simp only [if_true] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      exact (flattenConclComposeSome (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _)
        (ih c1 s1 lt1 false (some x) s2 n l cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono
          (by simp)
  · -- else-branch never returns: placed first
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.label n l2 0 :: appListAppend xs)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instXs⟩ := labelAt instLab
    cases b
    · -- condition false: the else-branch produces a result
      have some_ := FlattenHelpers.noRetCorrect false c2 n l1 cs bs (by rw [h2]; exact k5) s1
      simp only [Bool.false_eq_true, if_false] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      exact (flattenConclComposeSome (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _)
        (ih c2 s1 lt2 false (some x) s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono
          (by simp)
    · -- condition true: jump to the then-branch
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine (flattenConclCompose (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _) ?_
        (ih c1 s1 lt1 false res s2 n l cs bs _
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono
          (by simp)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- general shape with a join jump
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0 :: .label n l2 0 ::
            (appListAppend xs ++ [.label n (l2 + 1) 0]))) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instRest2⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨fetchJ, instRest3⟩ := lineAt (nolab _) instRest2
    obtain ⟨locL, instRest4⟩ := labelAt instRest3
    obtain ⟨instXs, instLab2⟩ := codeInstalledAppendImp _ _ _ _ instRest4
    obtain ⟨locL2, -⟩ := labelAt instLab2
    have total : ((appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length +
          ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 2 := by
      rw [hflat]; simp [List.filter_append, isLabelHOL]; omega
    cases b
    · -- condition false: the else-branch, then the join jump
      simp only [Bool.false_eq_true, if_false] at evb
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      have c2h := ih c2 s1 lt2 false res s2 n l1 cs bs { t1 with pc := t1.pc + 1 }
        ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩
      cases res with
      | some x =>
        exact (flattenConclComposeSome (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
          (List.prefix_refl _) c2h).mono (by simp)
      | none =>
        obtain ⟨ck2, t3, hb2, run2, f1, f2, f3, f4, f5, pre2, hpc2, rel3⟩ := flattenConclNone c2h
        rw [h2] at hpc2
        simp only at hpc2 f1 f2 f3 f4 f5 pre2
        have fetchJ3 : asmFetchAux t3.pc t3.code =
            some (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0) := by
          rw [hpc2]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre2⟩
        have locL23 := locToPcIsPrefix _ _ _ _ _ ⟨locL2, pre2⟩
        refine ⟨1 + ck2 + 1, { t3 with pc := t1.pc + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length },
          by simp at hb2 ⊢; omega, fun ck1 => ?_, f1, f2, f3, f4, f5, pre2, ?_, rel3⟩
        · rw [show t1.clock + (1 + ck2 + 1) + ck1 = t1.clock + 1 + (ck2 + (ck1 + 1)) by omega,
            runToPc step, show t1.clock + (ck2 + (ck1 + 1)) = t1.clock + ck2 + (ck1 + 1) by omega,
            run2, show t3.clock + (ck1 + 1) = (t3.clock + ck1) + 1 by omega,
            jumpStep (t3.clock + ck1) fetchJ3 locL23]
        · simp only [total]; omega
    · -- condition true: jump to the then-branch
      simp only [if_true] at evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine (flattenConclCompose (a := 1) (by simp) (runToPc step) rfl rfl rfl rfl
        rfl
        (List.prefix_refl _) ?_
        (ih c1 s1 lt1 false res s2 n l cs bs _
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono
          (by simp)
      rw [total, h1]
      simp
      omega

end

end SteppedFlapjack.StackToLabSteps
