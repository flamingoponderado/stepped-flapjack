import SteppedFlapjack.StackAllocSteps.AllocPassSteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.AllocStore
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open SteppedFlapjack.StackSteps
/-- The generated store-constants call takes at most five steps. -/
theorem storeStubCallStepBound {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 loc n m : Nat) (s : StackSemStateFiniteExact width C F)
    (hfind : findCode (.inl loc) (s.regs.eraseEq 0) s.code =
      some (.seq (.storeConsts t1 t2 none) (.ret 0))) :
    steps (.call (some (.skip, 0, n, m)) (.inl loc) none, s) ≤ 5 := by
  rw [steps_call_some]
  simp only [hfind]
  split
  · simp
  · rw [steps_seq]
    have hstore : ∀ t : StackSemStateFiniteExact width C F, steps (.storeConsts t1 t2 none, t) = 1 := by
      intro t
      exact steps_leaf _ _ rfl
    rw [hstore]
    have hret : ∀ t : StackSemStateFiniteExact width C F, steps (.ret 0, t) = 1 := by
      intro t
      exact steps_leaf _ _ rfl
    have hskip : ∀ t : StackSemStateFiniteExact width C F, steps (.skip, t) = 1 := by
      intro t
      exact steps_leaf _ _ rfl
    split <;> split <;> (try simp only [hret, hskip])
    all_goals (try split_ifs) <;> simp +arith

open StackSemStoreConstsGuard in
/-- The store-constants pass case needs at most five target steps. -/
theorem goalStoreConstsSteps {width : Nat} [NeZero width] {C F : Type}
    (anything : WordSemGcFun width) (cr : CompileFn width C)
    (s : StackSemStateFiniteExact width C F) (t1 t2 : Nat) (stub : Option Nat) :
    ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (c : DataToWord.Config) (regs : HolFiniteMapExact Nat (WordLocW width)),
    evaluate (.storeConsts t1 t2 stub, s) = (r, t) → r ≠ some .error →
    StackProps.allocArg (.storeConsts t1 t2 stub : HolProg width) → Pre cr c s regs →
    ∃ ck regs1,
      evaluate ((comp n m (.storeConsts t1 t2 stub)).1, Tgt anything cr c s ck regs) =
        (r, Res anything cr c t regs1) ∧ Post r t regs1 ∧
      steps ((comp n m (.storeConsts t1 t2 stub)).1, Tgt anything cr c s ck regs) ≤ 5 := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_storeConsts] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hS
  rw [if_neg (by simp [hpre.useAlloc])] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hchk
  have hR : (s.regs.eraseEq 0).submap regs := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hk
    split at hk
    · simp at hk
    · exact hpre.regs _ _ hk
  cases stub with
  | none =>
      obtain ⟨R1, he, hsub, -, -, -, hst, hbuf⟩ :=
        storeConstSem_res anything cr c s t regs hR hpre.useAlloc t1 t2 r hr h
      refine ⟨0, R1, ?_, ⟨hsub, hbuf ▸ hpre.buf, fun _ => by unfold StackBound; rw [hst]; exact hpre.stack⟩, ?_⟩
      show evaluate (.storeConsts t1 t2 none, Res anything cr c s regs) = _
      rw [evaluate_storeConsts]
      simp only [not_true_eq_false, if_false, Option.isSome_none, Bool.false_eq_true, and_false]
      simp only [checkStoreConstsOpt, not_true_eq_false, if_false]
      exact he
      · change steps (.storeConsts t1 t2 none, Tgt anything cr c s 0 regs) ≤ 5
        rw [steps_leaf _ _ rfl]
        decide
  | some loc =>
      have hlk : sptLookup loc s.code = some (.seq (.storeConsts t1 t2 none) (.ret 0)) :=
        (checkStoreConstsOpt_some_iff t1 t2 loc s.code).1 (by simpa using hchk)
      have hloc := (hpre.code loc _ hlk).1
      obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hlk, hloc⟩
      have hR' : (s.regs.eraseEq 0).submap (regs.updateEq (0, .loc n m)) := by
        intro k v hk
        simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hk
        split at hk
        · simp at hk
        · rename_i hk0
          simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg hk0]
          exact hpre.regs _ _ hk
      obtain ⟨R1, he, hsub, h0, rfl, hclk, hst, hbuf⟩ :=
        storeConstSem_res anything cr c s t (regs.updateEq (0, .loc n m)) hR' hpre.useAlloc t1 t2 r
          hr h
      refine ⟨1, R1, ?_, ⟨hsub, hbuf ▸ hpre.buf, fun _ => by unfold StackBound; rw [hst]; exact hpre.stack⟩, ?_⟩
      show evaluate (.call (some (.skip, 0, n, m)) (.inl loc) none, Tgt anything cr c s 1 regs) = _
      rw [evaluate_call]
      simp only [StackSemControl.findCode]
      rw [hcl]
      simp only [comp]
      rw [if_neg (by simp)]
      have hds : decClock (setVar 0 (.loc n m) (Tgt anything cr c s 1 regs)) =
          Res anything cr c s (regs.updateEq (0, .loc n m)) := rfl
      rw [hds, evaluate_seq, evaluate_storeConsts]
      simp only [not_true_eq_false, if_false, Option.isSome_none, Bool.false_eq_true, and_false,
        checkStoreConstsOpt]
      rw [he]
      simp only [StackSemControl.fixClock, hclk, Nat.min_self]
      rw [evaluate_ret]
      have hg0 : getVar 0 { Res anything cr c t R1 with clock := s.clock } = some (.loc n m) := by
        show R1.lookup 0 = _
        rw [h0]
        simp [FUPDATE_HOL]
      rw [hg0]
      simp only [ne_eq, not_true_eq_false, if_false, evaluate_skip]
      simp [hclk]

      · change steps (.call (some (.skip, 0, n, m)) (.inl loc) none,
          Tgt anything cr c s 1 regs) ≤ 5
        apply storeStubCallStepBound
        simpa [Tgt, StackSemControl.findCode, comp] using hcl

end SteppedFlapjack.StackAllocSteps
