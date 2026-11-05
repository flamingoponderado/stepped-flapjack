import SteppedFlapjack.StackAllocSteps.CallSteps
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.StackSemMeasure Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Returning calls preserve a common factor for the callee and continuation. -/
theorem boundedCallSome (anything : WordSemGcFun width) (cr : CompileFn width C)
    (K : Nat) (hK : 1 ≤ K) (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (retH : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ih : ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
      LexNat (stackSemMeasure q u) (stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s) → BoundedGoal anything cr K c q u) :
    BoundedGoal anything cr K c (.call (some (retH, link, l1, l2)) dest handler) s := by
  intro r t m n regs h hr ha hpre
  unfold StackProps.allocArg at ha
  obtain ⟨haR, haH⟩ := ha
  replace haR : StackProps.allocArg retH := haR
  rw [evaluate_call] at h
  dsimp only at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨k, hk, hfeq⟩ :=
    find_code_IMP_lookup (find_code_regs_SUBMAP ⟨submap_domsub_both (c := link) hpre.regs, hprog⟩)
  obtain ⟨hgc, hap⟩ := hpre.code k prog hk
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hk, hgc⟩
  have hf : StackSemControl.findCode dest (regs.eraseEq link)
      (sptFromAList (compile c (sptToAList s.code))) = some (comp m1 n1 prog).1 := by
    rw [hfeq]; exact hcl
  by_cases h0 : s.clock = 0
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, ?_, ⟨submap_empty _, hpre.buf, fun _ => ?_⟩, ?_⟩
    · rw [comp_callSome, evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      simp only [tgt_zero, h0, if_true]
      rfl
    · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
      exact Nat.two_pow_pos width
    · rw [comp_callSome, steps_call_some, steps_call_some]
      have htfind : findCode dest ((Tgt anything cr c s 0 regs).regs.eraseEq link)
          (Tgt anything cr c s 0 regs).code = some (comp m1 n1 prog).1 := hf
      simp only [htfind, hprog]
      simpa [Tgt, h0] using hK
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at h
  have h0' : (StackSemStateOps.setVar link (.loc l1 l2) s).clock ≠ 0 := h0
  rcases h1 : evaluate (prog, decClock (StackSemStateOps.setVar link (.loc l1 l2) s)) with ⟨res, s2⟩
  rw [h1] at h
  have hres : res ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at h
    exact hr h.1.symm
  have hmc : LexNat (stackSemMeasure prog (decClock (StackSemStateOps.setVar link (.loc l1 l2) s)))
      (stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s) := by
    have := callee_measure_lt prog (.call (some (retH, link, l1, l2)) dest handler) _ h0'
    rwa [measure_setVar_call] at this
  have hpreC := (hpre.setVar link (.loc l1 l2)).decClock
  obtain ⟨ck1, regs1, he1, ⟨hsub1, hbuf1, hst1⟩, hs1⟩ :=
    ih prog _ hmc res s2 n1 m1 _ h1 hres hap hpreC
  -- the target call site
  have hsite : ∀ ck, decClock (StackSemStateOps.setVar link (.loc l1 l2) (Tgt anything cr c s ck regs)) =
      Tgt anything cr c (decClock (StackSemStateOps.setVar link (.loc l1 l2) s)) ck
        (regs.updateEq (link, .loc l1 l2)) :=
    fun ck => callSite_tgt anything cr c s regs ck link _ h0
  have hcont : ∀ (q : HolProg width), LexNat (stackSemMeasure q s2)
      (stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s) := by
    intro q
    have := call_continuation_measure_lt q (.call (some (retH, link, l1, l2)) dest handler) s link l1
      l2 (evaluate (prog, decClock (StackSemStateOps.setVar link (.loc l1 l2) s))) h0
    rwa [StackSemEvaluateClock.fixClockEvaluate, h1] at this
  -- the callee in the target, with `ck2` more clock when it does not time out
  have hcallee : ∀ ck2, (ck2 = 0 ∨ res ≠ some .timeOut) →
      evaluate ((comp m1 n1 prog).1, Tgt anything cr c (decClock (StackSemStateOps.setVar link
        (.loc l1 l2) s)) (ck1 + ck2) (regs.updateEq (link, .loc l1 l2))) =
        (res, Tgt anything cr c s2 ck2 regs1) := by
    rintro ck2 (rfl | hto)
    · exact he1
    · exact target_add_clock anything cr he1 hto ck2
  -- the continuation shape of the target evaluation
  have htgt : ∀ ck2, (ck2 = 0 ∨ res ≠ some .timeOut) →
      evaluate (.call (some ((comp n m retH).1, link, l1, l2)) dest
        (compHandler n (comp n m retH).2 handler), Tgt anything cr c s (ck1 + ck2) regs) =
      match (res, Tgt anything cr c s2 ck2 regs1) with
      | (some (.result x), s2) =>
          if x ≠ .loc l1 l2 then (some .error, s2) else evaluate ((comp n m retH).1, s2)
      | (some (.exception x), s2) =>
          match compHandler n (comp n m retH).2 handler with
          | none => (some (.exception x), s2)
          | some (h, hl1, hl2) =>
              if x ≠ .loc hl1 hl2 then (some .error, s2) else evaluate (h, s2)
      | (none, s2) => (some .error, s2)
      | (some (.break _), s2) => (some .error, s2)
      | (some (.continue _), s2) => (some .error, s2)
      | (res, s2) => (res, s2) := by
    intro ck2 hck
    rw [evaluate_call]
    dsimp only
    rw [hf]
    dsimp only
    rw [if_neg (by show s.clock + (ck1 + ck2) ≠ 0; omega), StackSemEvaluateClock.fixClockEvaluate,
      hsite, hcallee ck2 hck]
    rfl
  have hcountS : steps (.call (some (retH, link, l1, l2)) dest handler, s) =
      1 + steps (prog, decClock (setVar link (.loc l1 l2) s)) +
        (match (res, s2) with
        | (some (.result x), st) => if x = .loc l1 l2 then steps (retH, st) else 0
        | (some (.exception x), st) =>
            match handler with
            | some (hp, k1, k2) => if x = .loc k1 k2 then steps (hp, st) else 0
            | none => 0
        | _ => 0) := by
    rw [steps_call_some]
    simp only [hprog, if_neg h0]
    rw [StackSemEvaluateClock.fixClockEvaluate, h1]
    simp only [Nat.add_assoc]
    split <;> simp_all only [Prod.mk.injEq]
    all_goals simp_all
    all_goals split <;> simp_all
  have hcountT : ∀ ck2, (ck2 = 0 ∨ res ≠ some .timeOut) →
      steps (.call (some ((comp n m retH).1, link, l1, l2)) dest
        (compHandler n (comp n m retH).2 handler), Tgt anything cr c s (ck1 + ck2) regs) =
      1 + steps ((comp m1 n1 prog).1, Tgt anything cr c (decClock (setVar link (.loc l1 l2) s))
        (ck1 + ck2) (regs.updateEq (link, .loc l1 l2))) +
        (match (res, Tgt anything cr c s2 ck2 regs1) with
        | (some (.result x), st) => if x = .loc l1 l2 then steps ((comp n m retH).1, st) else 0
        | (some (.exception x), st) =>
            match compHandler n (comp n m retH).2 handler with
            | some (hp, k1, k2) => if x = .loc k1 k2 then steps (hp, st) else 0
            | none => 0
        | _ => 0) := by
    intro ck2 hck
    rw [steps_call_some]
    dsimp only
    rw [hf]
    simp only [if_neg (by show s.clock + (ck1 + ck2) ≠ 0; omega)]
    rw [hsite, StackSemEvaluateClock.fixClockEvaluate, hcallee ck2 hck]
    simp only [Nat.add_assoc]
    split <;> simp_all only [Prod.mk.injEq]
    all_goals simp_all
    all_goals split <;> simp_all
  have hcountBoost : ∀ ck2, res ≠ some .timeOut →
      steps ((comp m1 n1 prog).1, Tgt anything cr c (decClock (setVar link (.loc l1 l2) s))
        (ck1 + ck2) (regs.updateEq (link, .loc l1 l2))) =
      steps ((comp m1 n1 prog).1, Tgt anything cr c (decClock (setVar link (.loc l1 l2) s))
        ck1 (regs.updateEq (link, .loc l1 l2))) := by
    intro ck2 hne
    rw [tgt_add]
    exact steps_addClock ck2 _ _ _ rfl res _ he1 hne
  have hpre2 : ∀ x, res = some (.result x) ∨ res = some (.exception x) →
      Pre cr c s2 regs1 := by
    rintro x (rfl | rfl) <;> exact Pre.of_evaluate h1 hpreC hsub1 hbuf1 (hst1 (by simp))
  rcases res with _ | ⟨x | x | _ | _ | w | _ | ev | _⟩
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · -- Result
    dsimp only at h
    by_cases hx : x = .loc l1 l2
    · rw [if_neg (not_not.2 hx)] at h
      obtain ⟨ck2, regs2, he2, hpost2, hs2⟩ :=
        ih retH s2 (hcont retH) r t m n regs1 h hr haR (hpre2 x (Or.inl rfl))
      refine ⟨ck1 + ck2, regs2, ?_, hpost2, ?_⟩
      · rw [comp_callSome, htgt ck2 (Or.inr (by simp))]
        dsimp only
        rw [if_neg (not_not.2 hx)]
        exact he2
      · rw [comp_callSome, hcountT ck2 (Or.inr (by simp)), hcountS]
        simp only [hx, if_true]
        rw [hcountBoost ck2 (by simp)]
        simp only [Nat.mul_add, Nat.mul_one]
        omega
    · rw [if_pos hx] at h
      simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · -- Exception
    dsimp only at h
    rcases handler with _ | ⟨hp, k1, k2⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, regs1, ?_, ⟨hsub1, hbuf1, hst1⟩, ?_⟩
      · have h00 := htgt 0 (Or.inl rfl)
        simp only [Nat.add_zero] at h00
        rw [comp_callSome, h00]
        rfl
      · have hc := hcountT 0 (Or.inl rfl)
        simp only [Nat.add_zero] at hc
        rw [comp_callSome, hc, hcountS]
        simp only [compHandler, Nat.add_zero, Nat.mul_add, Nat.mul_one]
        omega
    · replace haH : StackProps.allocArg hp := haH
      dsimp only at h
      by_cases hx : x = .loc k1 k2
      · rw [if_neg (not_not.2 hx)] at h
        obtain ⟨ck2, regs2, he2, hpost2, hs2⟩ :=
          ih hp s2 (hcont hp) r t (comp n m retH).2 n regs1 h hr haH (hpre2 x (Or.inr rfl))
        refine ⟨ck1 + ck2, regs2, ?_, hpost2, ?_⟩
        · rw [comp_callSome, htgt ck2 (Or.inr (by simp))]
          dsimp only [compHandler]
          rw [if_neg (not_not.2 hx)]
          exact he2
        · rw [comp_callSome, hcountT ck2 (Or.inr (by simp)), hcountS]
          simp only [compHandler, hx, if_true]
          rw [hcountBoost ck2 (by simp)]
          simp only [Nat.mul_add, Nat.mul_one]
          omega
      · rw [if_pos hx] at h
        simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  all_goals
    dsimp only at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ck1, regs1, ?_, ⟨hsub1, hbuf1, hst1⟩, ?_⟩
    · have h00 := htgt 0 (Or.inl rfl)
      simp only [Nat.add_zero] at h00
      rw [comp_callSome, h00]
      rfl
    · have hc := hcountT 0 (Or.inl rfl)
      simp only [Nat.add_zero] at hc
      rw [comp_callSome, hc, hcountS]
      simp only [Nat.add_zero, Nat.mul_add, Nat.mul_one]
      omega

end SteppedFlapjack.StackAllocSteps
