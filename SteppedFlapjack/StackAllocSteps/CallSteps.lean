import SteppedFlapjack.StackAllocSteps.JumpSteps
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.StackSemMeasure Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Tail calls preserve a common subrun step factor. -/
theorem boundedCallNone (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.call none dest handler) s) → BoundedGoal anything cr K c q u) :
    BoundedGoal anything cr K c (.call none dest handler) s := by
  intro r t m n regs h hr _ hpre
  rw [evaluate_call] at h
  dsimp only at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨k, hk, hfeq⟩ := find_code_IMP_lookup (find_code_regs_SUBMAP ⟨hpre.regs, hprog⟩)
  obtain ⟨hgc, hap⟩ := hpre.code k prog hk
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hk, hgc⟩
  have hf : StackSemControl.findCode dest regs (sptFromAList (compile c (sptToAList s.code))) =
      some (comp m1 n1 prog).1 := by rw [hfeq]; exact hcl
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  by_cases h0 : s.clock = 0
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, ?_, ⟨submap_empty _, hpre.buf, fun _ => ?_⟩, ?_⟩
    · change evaluate (.call none dest none, _) = _
      rw [evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      simp only [tgt_zero, h0, if_true]
      rfl
    · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
      exact Nat.two_pow_pos width
    · change steps (.call none dest none, _) ≤ _
      rw [steps_call_none, steps_call_none]
      simpa [hprog, hf, h0] using hK
  · rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at h
    rcases h1 : evaluate (prog, decClock s) with ⟨res, s2⟩
    rw [h1] at h
    dsimp only at h
    have hres : res ≠ some .error := by
      rintro rfl
      simp [StackSemControl.badFunReturn] at h
      exact hr h.1.symm
    obtain ⟨ck, regs1, he, hpost, hs⟩ :=
      ih prog (decClock s) (callee_measure_lt prog _ s h0) res s2 n1 m1 regs h1 hres hap
        hpre.decClock
    refine ⟨ck, regs1, ?_, ?_, ?_⟩
    · change evaluate (.call none dest none, _) = _
      rw [evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      rw [if_neg (by show s.clock + ck ≠ 0; omega), StackSemEvaluateClock.fixClockEvaluate,
        decClock_tgt anything cr c s regs ck h0, he]
      dsimp only
      split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · rw [if_neg ‹_›]
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hpost

    · change steps (.call none dest none, _) ≤ _
      rw [steps_call_none, steps_call_none]
      have htfind : findCode dest (Tgt anything cr c s ck regs).regs
          (Tgt anything cr c s ck regs).code = some (comp m1 n1 prog).1 := hf
      simp only [htfind, hprog, if_neg h0, if_neg (by show s.clock + ck ≠ 0; omega)]
      rw [decClock_tgt anything cr c s regs ck h0]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
end SteppedFlapjack.StackAllocSteps
