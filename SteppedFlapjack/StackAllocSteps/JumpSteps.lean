import SteppedFlapjack.StackAllocSteps.ControlSteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Calls
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.StackSemMeasure Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- An indirect jump adds one step to the executed code's bound. -/
theorem boundedJumpLower (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (s : StackSemStateFiniteExact width C F) (r1 r2 dest : Nat)
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.jumpLower r1 r2 dest) s) → BoundedGoal anything cr K q u) :
    BoundedGoal anything cr K (.jumpLower r1 r2 dest) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_jumpLower] at h
  split at h
  · rename_i x y hx hy
    have gx : ∀ ck, getVar r1 (Tgt anything cr c s ck regs) = some (.word x) :=
      fun _ => hpre.regs _ _ hx
    have gy : ∀ ck, getVar r2 (Tgt anything cr c s ck regs) = some (.word y) :=
      fun _ => hpre.regs _ _ hy
    split at h
    · rename_i hlt
      split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      rename_i prog hprog
      have hprog' : sptLookup dest s.code = some prog := hprog
      obtain ⟨hk, hap⟩ := hpre.code dest prog hprog'
      obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hprog', hk⟩
      have hf : findCode (.inl dest) regs
          (sptFromAList (compile c (sptToAList s.code))) = some (comp m1 n1 prog).1 := hcl
      by_cases h0 : s.clock = 0
      · rw [if_pos h0] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, HolFiniteMapExact.empty, ?_, ⟨submap_empty _, hpre.buf, fun _ => ?_⟩, ?_⟩
        · change evaluate (.jumpLower r1 r2 dest, _) = _
          rw [evaluate_jumpLower, gx, gy]
          simp only [hlt, if_true]
          rw [hf]
          simp only [tgt_zero, h0, if_true]
          rfl
        · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
          exact Nat.two_pow_pos width
        · change steps (.jumpLower r1 r2 dest, _) ≤ _
          rw [steps_jumpLower, steps_jumpLower]
          simp only [gx, gy, hx, hy, hlt, if_true]
          have htfind : findCode (.inl dest) (Tgt anything cr c s 0 regs).regs
              (Tgt anything cr c s 0 regs).code = some (comp m1 n1 prog).1 := hf
          rw [htfind, hprog]
          simpa [Tgt, h0] using hK
      · rw [if_neg h0] at h
        rcases h1 : evaluate (prog, decClock s) with ⟨res, s2⟩
        rw [h1] at h
        dsimp only at h
        have hres : res ≠ some .error := by
          rintro rfl
          simp [badFunReturn] at h
          exact hr h.1.symm
        obtain ⟨ck, regs1, he, hpost, hs⟩ :=
          ih prog (decClock s) (callee_measure_lt prog _ s h0) res s2 n1 m1 c regs h1 hres hap
            hpre.decClock
        refine ⟨ck, regs1, ?_, ?_, ?_⟩
        · change evaluate (.jumpLower r1 r2 dest, _) = _
          rw [evaluate_jumpLower, gx, gy]
          simp only [hlt, if_true]
          rw [hf]
          dsimp only
          rw [if_neg (by show s.clock + ck ≠ 0; omega), decClock_tgt anything cr c s regs ck h0, he]
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
        · change steps (.jumpLower r1 r2 dest, _) ≤ _
          rw [steps_jumpLower, steps_jumpLower]
          simp only [gx, gy, hx, hy, hlt, if_true]
          have htfind : findCode (.inl dest) (Tgt anything cr c s ck regs).regs
              (Tgt anything cr c s ck regs).code = some (comp m1 n1 prog).1 := hf
          have hsfind : findCode (.inl dest) s.regs s.code = some prog := hprog
          rw [htfind, hsfind]
          simp only [if_neg h0, if_neg (by show s.clock + ck ≠ 0; omega)]
          rw [decClock_tgt anything cr c s regs ck h0]
          simp only [Nat.mul_add, Nat.mul_one]
          omega
    · rename_i hn
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, regs, ?_, ⟨hpre.regs, hpre.buf, fun _ => hpre.stack⟩, ?_⟩
      · change evaluate (.jumpLower r1 r2 dest, _) = _
        rw [evaluate_jumpLower, gx, gy]
        dsimp only
        rw [if_neg hn]
        rfl
      · change steps (.jumpLower r1 r2 dest, _) ≤ _
        rw [steps_jumpLower, steps_jumpLower]
        simp [gx, gy, hx, hy, hn, hK]
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
/-- A raw call adds one step to the executed code's bound. -/
theorem boundedRawCall (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (s : StackSemStateFiniteExact width C F) (dest : Nat)
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.rawCall dest) s) → BoundedGoal anything cr K q u) :
    BoundedGoal anything cr K (.rawCall dest) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_rawCall] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨hk, hap⟩ := hpre.code dest prog hprog
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hprog, hk⟩
  split at h
  · rename_i p0 body hds
    cases prog with
    | seq a b =>
      simp only [StackSemControl.destSeq, Option.some.injEq, Prod.mk.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      have hap2 : allocArg b := hap.2
      have hcl' : ∀ ck, sptLookup dest (Tgt anything cr c s ck regs).code =
          some (.seq (comp m1 n1 a).1 (comp m1 (comp m1 n1 a).2 b).1) := fun _ => hcl
      by_cases h0 : s.clock = 0
      · rw [if_pos h0] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, HolFiniteMapExact.empty, ?_, ⟨submap_empty _, hpre.buf, fun _ => ?_⟩, ?_⟩
        · change evaluate (.rawCall dest, _) = _
          rw [evaluate_rawCall, hcl']
          simp only [StackSemControl.destSeq, tgt_zero, h0, if_true]
          rfl
        · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
          exact Nat.two_pow_pos width
        · change steps (.rawCall dest, _) ≤ _
          rw [steps_rawCall, steps_rawCall, hcl', hprog]
          simp [destSeq, h0, hK]
      · rw [if_neg h0] at h
        rcases h1 : evaluate (b, decClock s) with ⟨res, s2⟩
        rw [h1] at h
        dsimp only at h
        have hres : res ≠ some .error := by
          rintro rfl
          simp [StackSemControl.badFunReturn] at h
          exact hr h.1.symm
        obtain ⟨ck, regs1, he, hpost, hs⟩ :=
          ih b (decClock s) (callee_measure_lt b _ s h0) res s2 (comp m1 n1 a).2 m1 c regs
            h1 hres hap2 hpre.decClock
        refine ⟨ck, regs1, ?_, ?_, ?_⟩
        · change evaluate (.rawCall dest, _) = _
          rw [evaluate_rawCall, hcl']
          simp only [StackSemControl.destSeq]
          rw [if_neg (by show s.clock + ck ≠ 0; omega), decClock_tgt anything cr c s regs ck h0, he]
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
        · change steps (.rawCall dest, _) ≤ _
          rw [steps_rawCall, steps_rawCall, hcl', hprog]
          simp only [destSeq, if_neg h0, if_neg (by show s.clock + ck ≠ 0; omega)]
          rw [decClock_tgt anything cr c s regs ck h0]
          simp only [Nat.mul_add, Nat.mul_one]
          omega
    | _ => simp [StackSemControl.destSeq] at hds
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

end SteppedFlapjack.StackAllocSteps
