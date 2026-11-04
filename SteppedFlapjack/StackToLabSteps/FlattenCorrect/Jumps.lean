import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Loop

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Jumps.lean`
(stepped-flapjack#2, phase C1): the `JumpLower` and `RawCall` cases for
`FlattenPropWithin`. Each runs one LabSem instruction of its own, the jump,
before the procedure body, whose run is bounded by the steps of the body.
Otherwise the statements and proofs follow the original. -/

/-! `flatten_correct` cases `JumpLower` and `RawCall`
(`stack_to_labProofScript.sml:1881-2010`): both jump into a procedure that
`state_rel` guarantees is installed, and use the induction hypothesis for the
procedure body at the decremented clock. -/

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

/-- Results other than `Break`/`Continue` have a result view independent of
the section and label stacks. -/
theorem resultViewIndep {x : StackSemResult width}
    (h : ¬StackSemControl.badFunReturn (some x) = true) (n n' : Nat) (cs bs cs' bs' : List Nat) :
    resultView x n cs bs = resultView x n' cs' bs' := by
  rcases x with v | v | k | k | v | _ | o | _ <;>
    first | (cases v <;> rfl) | rfl | simp [StackSemControl.badFunReturn] at h

/-- Installed procedures of the source code map. -/
theorem relCode {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) {k : Nat}
    {prog : HolProg width} (h : sptLookup k s.code = some prog) :
    Compiler.Backend.StackProps.callArgs prog t.ptrReg t.lenReg t.ptr2Reg t.len2Reg t.linkReg ∧
      ∃ pc, codeInstalled pc (appListAppend (flattenHOL true prog k
          (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []).1) t.code ∧ locToPc k 0 t.code =
              some pc :=
  rel.2.2.2.2.2.2.2.2.1 k prog h

/-- A jump entered with one clock tick, as a zero-clock prefix run. -/
theorem runEnter {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {p : Nat}
    (h0 : t1.clock ≠ 0)
    (step : ∀ c, evaluate { t1 with clock := c + 1 } = evaluate { t1 with pc := p, clock := c }) :
    ∀ ck1, evaluate { t1 with clock := t1.clock + 0 + ck1 } =
      evaluate { ({ t1 with pc := p, clock := t1.clock - 1 } :
        Flapjack.Compiler.Backend.LabSem.State width C F) with
        clock := t1.clock - 1 + ck1 } := by
  intro ck1
  rw [show t1.clock + 0 + ck1 = (t1.clock - 1 + ck1) + 1 by omega, step]

/-- `JumpLower` case. -/
theorem flattenCorrectJumpLower (s1 : StackSemStateFiniteExact width C F) (r1 r2 dest : Nat)
    (ih : FlattenIHWithin (.jumpLower r1 r2 dest) s1) : FlattenPropWithin (.jumpLower r1 r2 dest)
        s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_jumpLower] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jumpCmp .lower r1 (.reg r2) (.lab dest 0)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  rcases hx : StackSemStateOps.getVar r1 s1 with _ | ⟨x | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar r2 s1 with _ | ⟨y | ⟨_, _⟩⟩ <;>
    simp only [hx, hy] at ev <;> try exact (err ev).elim
  have hcmp : wordSemWordCmp .lower (t1.regs r1) (regImm (.reg r2) t1) =
      some (wordCmpHOL .lower x y) := by
    simp [regImm, InstCorrect.regOfLookup rel hx, InstCorrect.regOfLookup rel hy, wordSemWordCmp]
  have clk := relClock rel
  by_cases hlow : wordCmpHOL .lower x y = true
  · rw [if_pos hlow] at ev
    rw [hlow] at hcmp
    split at ev
    · exact (err ev).elim
    rename_i prog hfind
    have hlook : sptLookup dest s1.code = some prog := by
      simpa [StackSemControl.findCode] using hfind
    obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
    by_cases h0 : s1.clock = 0
    · rw [if_pos h0] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, t1, by simp, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel]
      · omega
    · rw [if_neg h0] at ev
      rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
      rw [e2] at ev
      simp only at ev
      by_cases hbad : StackSemControl.badFunReturn res = true
      · rw [if_pos hbad] at ev; exact (err ev).elim
      rw [if_neg hbad] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
      have rel' : stateRel (StackSemStateOps.decClock s1)
          { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
      have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.jumpLower r1 r2 dest) s1 :=
        .inl (by simp [StackSemStateOps.decClock]; omega)
      have ph := ih prog _ lt true (some x') s' dest (Compiler.Backend.StackAlloc.nextLabHOL prog
          2) [] []
        { t1 with pc := pc', clock := t1.clock - 1 }
        ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
      have step := fun c => (jumpCmpStep (b := true) c fetch hcmp)
      simp only [if_true, entry] at step
      refine (flattenConclComposeSome (a := 1) (by simp only; omega) (runEnter (by omega) step)
        rfl rfl rfl rfl rfl (List.prefix_refl _)
        (flattenConclResult (p' := prog) (t' := true) (l' := 0) (h := ph) rfl
          (resultViewIndep hbad _ _ _ _ _ _))).mono ?_
      rw [steps_jumpLower, hx, hy]
      simp only [hlow, if_true, hfind, h0, if_false, flattenStepFactor]
      omega
  · have hlow' : wordCmpHOL .lower x y = false := by simpa using hlow
    rw [if_neg hlow] at ev
    rw [hlow'] at hcmp
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have step := fun c => (jumpCmpStep (b := false) c fetch hcmp)
    simp only [Bool.false_eq_true, if_false] at step
    refine ⟨1, { t1 with pc := t1.pc + 1 }, oneStepBound (by simp [flattenStepFactor]),
      runToPc step, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, rel⟩
    simp [flattenHOL, appListAppendList, isLabelHOL]

/-- `RawCall` case. -/
theorem flattenCorrectRawCall (s1 : StackSemStateFiniteExact width C F) (dest : Nat)
    (ih : FlattenIHWithin (.rawCall dest) s1) : FlattenPropWithin (.rawCall dest) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_rawCall] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm (.jump (.lab dest 1)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hlook : sptLookup dest s1.code with _ | prog
  · rw [hlook] at ev; exact (err ev).elim
  rw [hlook] at ev
  simp only at ev
  rcases prog with _ | _ | _ | _ | _ | _ | ⟨p1,
      body⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals try (simp only [StackSemControl.destSeq] at ev; exact (err ev).elim)
  simp only [StackSemControl.destSeq] at ev
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  simp only [Compiler.Backend.StackProps.callArgs] at caP
  rcases h1 : flattenHOL false p1 dest (Compiler.Backend.StackAlloc.nextLabHOL (.seq p1 body) 2)
      [] [] with
    ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false body dest l1 [] [] with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (flattenHOL true (.seq p1 body) dest
      (Compiler.Backend.StackAlloc.nextLabHOL (.seq p1 body) 2) [] []).1 =
      appListAppend xs ++ (.label dest 1 0 :: appListAppend ys) := by
    rw [flattenHOL]; simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at instP
  obtain ⟨-, instRest⟩ := codeInstalledAppendImp _ _ _ _ instP
  obtain ⟨loc1, instYs⟩ := labelAt instRest
  set lenXs := ((appListAppend xs).filter (fun x => !isLabelHOL x)).length with hLenXs
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, t1, by simp, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  rcases e2 : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc' + lenXs, clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have lt : MeasureLt body (StackSemStateOps.decClock s1) (.rawCall dest) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := ih body _ lt false (some x') s' dest l1 [] []
    { t1 with pc := pc' + lenXs, clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP.2, by rw [h2]; exact instYs, by simp [entry]⟩
  have step := fun c => jumpStep c fetch loc1
  refine (flattenConclComposeSome (a := 1) (by simp only; omega) (runEnter (by omega) step)
    rfl rfl rfl rfl rfl (List.prefix_refl _)
    (flattenConclResult (p' := body) (t' := false) (l' := 0) (h := ph) rfl
      (resultViewIndep hbad _ _ _ _ _ _))).mono ?_
  rw [steps_rawCall, hlook]
  simp only [StackSemControl.destSeq, h0, if_false, flattenStepFactor]
  omega

end

end SteppedFlapjack.StackToLabSteps
