import SteppedFlapjack.StackAllocSteps.LeafSteps
import SteppedFlapjack.StackSteps.AddClock
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Control

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.StackSemMeasure Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

/-- A bounded simulation for one program, with a common factor for its subruns. -/
def BoundedGoal (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (c : DataToWord.Config) (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (m n : Nat) (regs : HolFiniteMapExact Nat (WordLocW width)),
    evaluate (p, s) = (r, t) → r ≠ some .error → StackProps.allocArg p → Pre cr c s regs →
    ∃ ck regs1, evaluate ((comp n m p).1, Tgt anything cr c s ck regs) =
        (r, Res anything cr c t regs1) ∧ Post r t regs1 ∧
      steps ((comp n m p).1, Tgt anything cr c s ck regs) ≤ K * steps (p, s)

/-- Sequence preserves a common factor supplied by its two recursive subruns. -/
theorem boundedSeq (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.seq c1 c2) s) → BoundedGoal anything cr K c q u) :
    BoundedGoal anything cr K c (.seq c1 c2) s := by
  intro r t m n regs h hr ha hpre
  obtain ⟨ha1, ha2⟩ := ha
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at h
  rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
  rw [h1] at h
  have hr1 : r1 ≠ some .error := by
    rintro rfl; simp only [Prod.mk.injEq] at h; exact hr h.1.symm
  obtain ⟨ck1, regs1, he1, hpost1, hs1⟩ :=
    ih c1 s (seq_first_measure_lt c1 c2 s) r1 t1 m n regs h1 hr1 ha1 hpre
  obtain ⟨hsub1, hbuf1, hst1⟩ := hpost1
  cases r1 with
  | some x =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, regs1, ?_, ⟨hsub1, hbuf1, hst1⟩, ?_⟩
      · change evaluate (.seq (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) = _
        rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, he1]
      · change steps (.seq (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) ≤ _
        rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, he1]
        rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, h1]
        simp only [Nat.add_zero, Nat.mul_add, Nat.mul_one]
        omega
  | none =>
      have hm := seq_second_measure_lt c1 c2 s (evaluate (c1, s))
      rw [StackSemEvaluateClock.fixClockEvaluate, h1] at hm
      have hpre1 := Pre.of_evaluate h1 hpre hsub1 hbuf1 (hst1 (by simp))
      obtain ⟨ck2, regs2, he2, hpost2, hs2⟩ :=
        ih c2 t1 hm r t (comp n m c1).2 n regs1 h hr ha2 hpre1
      have hboost := target_add_clock anything cr he1 (by simp) ck2
      have hsteps := steps_addClock ck2 _ _ _ rfl none _ he1 (by simp)
      have heq : steps ((comp n m c1).1, Tgt anything cr c s (ck1 + ck2) regs) =
          steps ((comp n m c1).1, Tgt anything cr c s ck1 regs) := by
        rw [tgt_add]
        exact hsteps
      refine ⟨ck1 + ck2, regs2, ?_, hpost2, ?_⟩
      · change evaluate (.seq (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) = _
        rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hboost]
        exact he2
      · change steps (.seq (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) ≤ _
        rw [steps_seq_run _ _ _ _ hboost, heq, steps_seq_run _ _ _ _ h1]
        simp only [Nat.mul_add, Nat.mul_one]
        omega

/-- A conditional preserves a common bound of its chosen branch. -/
theorem boundedIte (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (cmp : Compiler.Encoders.Asm.HolCmp) (r1 : Nat) (ri : Compiler.Encoders.Asm.HolRegImm width)
    (c1 c2 : HolProg width)
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.ite cmp r1 ri c1 c2) s) → BoundedGoal anything cr K c q u) :
    BoundedGoal anything cr K c (.ite cmp r1 ri c1 c2) s := by
  intro r t m n regs h hr ha hpre
  obtain ⟨ha1, ha2⟩ := ha
  rw [evaluate_ite] at h
  split at h
  · rename_i x y hx hy
    split at h
    · rename_i hc
      obtain ⟨ck, regs1, he, hpost, hs⟩ :=
        ih c1 s (if_first_measure_lt cmp r1 ri c1 c2 s) r t m n regs h hr ha1 hpre
      refine ⟨ck, regs1, ?_, hpost, ?_⟩
      · change evaluate (.ite cmp r1 ri (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) = _
        rw [evaluate_ite, tgt_eq]
        rw [show getVar r1 { Res anything cr c s regs with clock := s.clock + ck } = some x from
            getVar_res anything cr c s regs hpre.regs hx,
          show StackSemStateOps.getVarImm ri.toWordRegImm { Res anything cr c s regs with clock := s.clock + ck } =
            some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
        simp only [hc]
        exact he
      · change steps (.ite cmp r1 ri (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) ≤ _
        rw [steps_ite, steps_ite]
        simp only [hx, hy, hc]
        rw [show getVar r1 (Tgt anything cr c s ck regs) = some x from getVar_res anything cr c s regs hpre.regs hx,
          show StackSemStateOps.getVarImm ri.toWordRegImm (Tgt anything cr c s ck regs) = some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
        simp only [hc, Nat.mul_add, Nat.mul_one]
        omega
    · rename_i hc
      obtain ⟨ck, regs1, he, hpost, hs⟩ :=
        ih c2 s (if_second_measure_lt cmp r1 ri c1 c2 s) r t (comp n m c1).2 n regs h hr ha2 hpre
      refine ⟨ck, regs1, ?_, hpost, ?_⟩
      · change evaluate (.ite cmp r1 ri (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) = _
        rw [evaluate_ite, tgt_eq]
        rw [show getVar r1 { Res anything cr c s regs with clock := s.clock + ck } = some x from
            getVar_res anything cr c s regs hpre.regs hx,
          show StackSemStateOps.getVarImm ri.toWordRegImm { Res anything cr c s regs with clock := s.clock + ck } =
            some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
        simp only [hc]
        exact he
      · change steps (.ite cmp r1 ri (comp n m c1).1 (comp n (comp n m c1).2 c2).1, _) ≤ _
        rw [steps_ite, steps_ite]
        simp only [hx, hy, hc]
        rw [show getVar r1 (Tgt anything cr c s ck regs) = some x from getVar_res anything cr c s regs hpre.regs hx,
          show StackSemStateOps.getVarImm ri.toWordRegImm (Tgt anything cr c s ck regs) = some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
        simp only [hc, Nat.mul_add, Nat.mul_one]
        omega
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr


/-- Loop iterations preserve a common factor supplied by their recursive subruns. -/
theorem boundedLoop (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F) (c1 : HolProg width)
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.loop c1) s) → BoundedGoal anything cr K c q u) :
    BoundedGoal anything cr K c (.loop c1) s := by
  intro r t m n regs h hr ha hpre
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at h
  rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
  rw [h1] at h
  dsimp only at h
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [StackSemControl.contLoop, StackSemControl.exitLoop] at h
    exact hr h.1.symm
  obtain ⟨ck1, regs1, he1, ⟨hsub1, hbuf1, hst1⟩, hs1⟩ :=
    ih c1 s (loop_body_measure_lt c1 s) r1 t1 m n regs h1 hr1 ha hpre
  by_cases hl : StackSemControl.contLoop r1 = true
  · have hnh : ∀ w, r1 ≠ some (.halt w) := by
      rcases contLoopImp r1 hl with rfl | rfl <;> simp
    have hnt : r1 ≠ some .timeOut := by
      rcases contLoopImp r1 hl with rfl | rfl <;> simp
    rw [if_pos hl] at h
    by_cases h0 : t1.clock = 0
    · rw [if_pos h0] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, HolFiniteMapExact.empty, ?_, ⟨submap_empty _, hbuf1, fun _ => ?_⟩, ?_⟩
      · change evaluate (.loop (comp n m c1).1, _) = _
        rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
        dsimp only
        rw [if_pos hl, if_pos h0]
        rfl
      · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
        exact Nat.two_pow_pos width
      · change steps (.loop (comp n m c1).1, _) ≤ _
        rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
        rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, h1]
        simp only [hl, h0, ne_eq, not_true_eq_false, and_false, if_false,
          Nat.add_zero, Nat.mul_add, Nat.mul_one]
        omega
    · rw [if_neg h0] at h
      have hm := loop_reentry_measure_lt c1 s (evaluate (c1, s))
      rw [StackSemEvaluateClock.fixClockEvaluate, h1] at hm
      have hpre1 := (Pre.of_evaluate h1 hpre hsub1 hbuf1 (hst1 hnh)).decClock
      obtain ⟨ck2, regs2, he2, hpost2, hs2⟩ :=
        ih (.loop c1) (decClock t1) (hm h0) r t m n regs1 h hr ha hpre1
      have hboost := target_add_clock anything cr he1 hnt ck2
      have hsteps := steps_addClock ck2 _ _ _ rfl r1 _ he1 hnt
      have heq : steps ((comp n m c1).1, Tgt anything cr c s (ck1 + ck2) regs) =
          steps ((comp n m c1).1, Tgt anything cr c s ck1 regs) := by
        rw [tgt_add]
        exact hsteps
      have hentry : decClock (Tgt anything cr c t1 ck2 regs1) =
          Tgt anything cr c (decClock t1) ck2 regs1 :=
        res_clock anything cr c (decClock t1) regs1 (by simp [decClock]; omega)
      have hclock : (Tgt anything cr c t1 ck2 regs1).clock ≠ 0 := by
        show t1.clock + ck2 ≠ 0
        omega
      refine ⟨ck1 + ck2, regs2, ?_, hpost2, ?_⟩
      · change evaluate (.loop (comp n m c1).1, _) = _
        rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, hboost]
        dsimp only
        rw [if_pos hl, if_neg hclock, hentry]
        exact he2
      · change steps (.loop (comp n m c1).1, _) ≤ _
        change steps (.loop (comp n m c1).1, Tgt anything cr c (decClock t1) ck2 regs1) ≤ _ at hs2
        rw [← heq] at hs1
        rw [steps_loop_run _ _ _ _ hboost hl hclock, hentry]
        rw [steps_loop_run _ _ _ _ h1 hl h0]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
  · rw [if_neg hl] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ck1, regs1, ?_, ⟨hsub1, hbuf1, fun hh => hst1 fun w hw => hh w ?_⟩, ?_⟩
    · change evaluate (.loop (comp n m c1).1, _) = _
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
      dsimp only
      rw [if_neg hl]
    · rw [hw]; rfl
    · change steps (.loop (comp n m c1).1, _) ≤ _
      rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
      rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, h1]
      simp [hl, Nat.mul_add]
      omega

end SteppedFlapjack.StackAllocSteps
