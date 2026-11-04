import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Statement
import Flapjack.Compiler.Backend.LabProps.ClockSupport

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Leaves.lean`
(stepped-flapjack#2, phase C1): the leaf cases for `FlattenPropWithin`. Each
leaf takes one step and its flattened code runs at most one LabSem instruction,
within the `flattenStepFactor` ticks of its step; `jumpRegLoc` also states that
bound. Otherwise the statements and proofs follow the original. -/

/-! `flatten_correct` cases for the one-line StackSem leaves `Halt`, `Inst`,
`Tick`, `Return`, `Raise`, `Break` and `Continue`
(`stack_to_labProofScript.sml:1219-1240`, `1268-1320`, `1460-1530`). -/

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

private theorem appList' {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

/-- A single installed non-label line is fetched at the installation point. -/
theorem fetchSingle {pc : Nat} {x : LabLineHOL width}
    {code : LabProgHOL width} (nl : isLabelHOL x = false)
    (h : codeInstalled pc [x] code) : asmFetchAux pc code = some x := by
  rw [codeInstalled_cons] at h
  simp only [nl, Bool.false_eq_true, if_false] at h
  exact h.1

theorem relClock {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    t.clock = s.clock := rel.2.2.2.2.2.2.2.1

theorem relFfi {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    t.ffi = s.ffi := rel.2.2.2.2.2.2.1

/-- `Halt` case. -/
theorem flattenCorrectHalt (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    FlattenPropWithin (.halt v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_halt] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  split at ev
  · rename_i w hw
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hreg : t1.regs t1.ptrReg = w := by
      rw [← ca]; exact InstCorrect.regOfLookup rel hw
    refine ⟨1, { t1 with clock := t1.clock + 1 }, leafBound rfl (by simp [flattenStepFactor]), ?_,
        ?_⟩
    · rw [evaluate]
      simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hreg]
      cases w with
      | word value =>
        by_cases hv : value = 0#width
        · simp [haltWordView, hv]
        · simp [haltWordView, hv]
      | loc a b => simp [haltWordView]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Inst` case. -/
theorem flattenCorrectInst (s1 : StackSemStateFiniteExact width C F) (i : HolInst width) :
    FlattenPropWithin (.inst i : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_inst] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst i)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  split at ev
  · rename_i s1' hi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have rel2 := InstCorrect.instCorrect ⟨hi, rel⟩
    obtain ⟨cpc, ccode, cclock, -, -, -, -, -, cptr, clen, cptr2, clen2, clink⟩ :=
      asmInstConsts i t1
    have nf := InstCorrect.notFailed rel2
    refine ⟨1, incPc (asmInst i t1),
      leafBound rfl (by simp [flattenStepFactor, incPc, cclock]), fun ck1 => ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, rel2⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
        Compiler.Backend.LabProps.asmInstWithClock, nf, Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock, cclock, cpc]
      congr 1 <;> first | omega | exact nf.symm
    all_goals simp [incPc, cptr, clen, cptr2, clen2, clink, ccode, cpc, flattenHOL, appList',
      isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- Every installed StackSem procedure has a LabSem entry position. -/
theorem codeLookupLocToPc {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    ∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t.code).isSome := by
  intro k hk
  obtain ⟨prog, hp⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨-, pc, -, entry⟩ := rel.2.2.2.2.2.2.2.2.1 k prog hp
  simp [entry]

/-- `Tick` case. -/
theorem flattenCorrectTick (s1 : StackSemStateFiniteExact width C F) :
    FlattenPropWithin (.tick : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_tick] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst .skip)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  have nf := InstCorrect.notFailed rel
  have clk := relClock rel
  split_ifs at ev with h0
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨1, incPc t1, leafBound rfl (by simp [flattenStepFactor, incPc]), fun ck1 => ?_, rfl,
        rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, StackSemStateOps.emptyEnv, relFfi rel]
    · simp [incPc]; omega
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, incPc (decClock t1),
      leafBound rfl (by simp [flattenStepFactor, incPc, decClock]; omega), fun ck1 => ?_, rfl,
          rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, StateRel.stateRelDecClock rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 0 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, decClock, flattenHOL, appList', isLabelHOL]

/-- Shared step of `Return` and `Raise`: a register jump to a `Loc`. -/
theorem jumpRegLoc {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {reg l1 l2 : Nat}
    (rel : stateRel s t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (hreg : t1.regs reg = .loc l1 l2) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      t1.clock + ck ≤ t2.clock + 1 ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      (∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t2.code).isSome) ∧
      ∀ w, locToPc l1 l2 t2.code = some w → w = t2.pc ∧ stateRel s t2 := by
  cases hpc : locToPc l1 l2 t1.code with
  | none =>
    refine ⟨1, { t1 with clock := t1.clock + 1 }, by simp, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, fun k hk => codeLookupLocToPc rel k hk, ?_⟩
    · simp only [Nat.add_assoc]
    · intro w hw; simp [hpc] at hw
  | some pc =>
    refine ⟨1, updPc pc t1, by simp [updPc], fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, codeLookupLocToPc rel, fun w hw => ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, hreg, hpc]
      congr 1
      simp only [updPc, decClock]
      congr 1
      omega
    · simp only [updPc] at hw ⊢
      rw [hpc] at hw
      exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `Return` case. -/
theorem flattenCorrectRet (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    FlattenPropWithin (.ret v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_ret] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨ck, t2, hb, h⟩ := jumpRegLoc rel fetch (InstCorrect.regOfLookup rel hv)
    exact ⟨ck, t2, leafBound rfl (by simp only [flattenStepFactor]; omega), h⟩
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Raise` case. -/
theorem flattenCorrectRaise (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    FlattenPropWithin (.raise v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_raise] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨ck, t2, hb, h⟩ := jumpRegLoc rel fetch (InstCorrect.regOfLookup rel hv)
    exact ⟨ck, t2, leafBound rfl (by simp only [flattenStepFactor]; omega), h⟩
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Break` case. -/
theorem flattenCorrectBreak (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    FlattenPropWithin (.break k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, labs⟩
  rw [StackSemEvaluate.evaluate_break] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jump (.lab n (findLabHOL k bs))) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  have some_ : (locToPc n (findLabHOL k bs) t1.code).isSome := by
    by_cases hm : findLabHOL k bs ∈ bs
    · exact labs _ (by simp [hm])
    · rw [notMemFindLabImp bs k hm]; exact labs 0 (by simp)
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  refine ⟨1, updPc pc t1, leafBound rfl (by simp [flattenStepFactor, updPc]), fun ck1 => ?_, rfl,
      rfl, rfl, rfl, rfl,
    List.prefix_refl _, codeLookupLocToPc rel, fun w hw => ?_⟩
  · rw [evaluate]
    simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue, hpc]
    congr 1
    simp only [updPc, decClock]
    congr 1
    omega
  · simp only [updPc] at hw ⊢
    rw [hpc] at hw
    exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `LocValue` case. -/
theorem flattenCorrectLocValue (s1 : StackSemStateFiniteExact width C F) (reg l1 l2 : Nat) :
    FlattenPropWithin (.locValue reg l1 l2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_locValue] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue reg (.lab l1 l2)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  split_ifs at ev with check
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨pc, hpc⟩ := StateRel.locCheckImpLocToPc ⟨check, rel⟩
    refine ⟨1, incPc (updReg reg (.loc l1 l2) t1), leafBound rfl (by simp [flattenStepFactor,
        incPc, updReg]),
      fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, StateRel.setVarUpdReg rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue,
        hpc, reduceCtorEq]
      congr 1
      simp only [incPc, decClock, updReg, labToLoc]
      congr 1
      omega
    · simp [incPc, updReg, flattenHOL, appList', isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

theorem stateRelWithCodeBuffer {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    (cb : WordSemBuffer width 8) :
    stateRel { s with codeBuffer := cb } { t with codeBuffer := cb } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, _, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, rfl, h23, h24, h25, h26, h27, h28, h29⟩

/-- `CodeBufferWrite` case. -/
theorem flattenCorrectCodeBufferWrite (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    FlattenPropWithin (.codeBufferWrite r1 r2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_codeBufferWrite] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.cbw r1 r2) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appList'] using inst)
  have cbEq : s1.codeBuffer = t1.codeBuffer := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split at ev
  · rename_i w1 w2 h1 h2
    split at ev
    · rename_i cb hcb
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨1, incPc { t1 with codeBuffer := cb }, leafBound rfl (by simp [flattenStepFactor,
          incPc]),
        fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, stateRelWithCodeBuffer rel cb⟩
      · rw [evaluate]
        simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
          InstCorrect.regOfLookup rel h1, InstCorrect.regOfLookup rel h2, ← cbEq, hcb]
        congr 1
        simp only [incPc, decClock]
        congr 1
        omega
      · simp [incPc, flattenHOL, appList', isLabelHOL]
    · simp only [Prod.mk.injEq] at ev
      exact absurd ev.1.symm nerr
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Continue` case. -/
theorem flattenCorrectContinue (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    FlattenPropWithin (.continue k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_continue] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  refine ⟨0, t1, leafBound rfl (by simp [flattenStepFactor]), fun ck1 => rfl, rfl, rfl, rfl, rfl,
      rfl, List.prefix_refl _, rel, ?_⟩
  simpa [flattenHOL, appList'] using inst

end

end SteppedFlapjack.StackToLabSteps
