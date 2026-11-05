import SteppedFlapjack.StackNamesSteps.CompCorrect
import SteppedFlapjack.StackSteps.Defs

/-! Step preservation for `stack_names` (stepped-flapjack#2, phase C2).

`stack_names` only renames registers, so it changes neither the control flow nor
the number of `evaluate` invocations: `steps_progCompHOL` proves

  `steps (progCompHOL f p, renameState c f s) = steps (p, s)`

under a bijective `find_name f` and `Pre`, the hypotheses of `comp_correct`.
The proof is an induction on the same clock-first `stackSemMeasure` as
`comp_correct`; at every recursive call the branch decisions of the step count
are matched through `get_var_find_name`, `get_var_imm_find_name`,
`find_code_rename_state`, `lookup_rename_state_code`, `set_var_find_name`,
`dec_clock_rename_state` and `fix_clock_rename_state`, and `comp_correct` is
used only to identify the outcome and final state of a callee run, so that the
continuation's state is the renamed one. The count is exact: no constant is
added.

`compCorrectWithin` conjoins this equation with `comp_correct`, and
`compCorrect_of_within` forgets it again.

This is stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.StackNamesSteps

open Flapjack Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open Flapjack.StackSemMeasure Flapjack.StackSemEvaluate
open SteppedFlapjack.StackSteps
open SteppedFlapjack.StackNamesSteps.CompCorrect

variable {width : Nat} [NeZero width] {C F : Type}
  {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}

/-- A `Call` with a return handler and no return program is a leaf: it fails
before evaluating anything. -/
theorem steps_call_none_some {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (h : HolProg width × Nat × Nat)
    (s : StackSemStateFiniteExact width C F) :
    steps ((.call none dest (some h) : HolProg width), s) = 1 := by
  rw [steps_call_none]
  rcases hp : findCode dest s.regs s.code with _ | prog <;> simp

/-- `comp_correct`'s hypotheses give the same `steps` for the renamed program. -/
theorem steps_measure (hf : Function.Bijective (findNameSpt f)) :
    ∀ (m : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = m → Pre c f s →
      steps (progCompHOL f p, renameState c f s) = steps (p, s) := by
  intro m
  induction m using Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ m ih =>
  intro p s hm hpre
  subst hm
  cases p
  case seq c1 c2 =>
    change steps (.seq (progCompHOL f c1) (progCompHOL f c2), renameState c f s) =
      steps (.seq c1 c2, s)
    rw [steps_seq, steps_seq]
    rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
    have hcomp := compCorrect (c := c) (f := f) c1 s r1 t1 ⟨h1, hf, hpre⟩
    rw [ih _ (seq_first_measure_lt c1 c2 s) c1 s rfl hpre]
    rw [hcomp]
    rw [fixClock_renameState]
    have hfx : fixClock s (r1, t1) = (r1, { t1 with clock := min s.clock t1.clock }) := rfl
    have hfx2 : (fixClock s (r1, t1)).2 = { t1 with clock := min s.clock t1.clock } := rfl
    rw [hfx2, hfx]
    cases r1 with
    | none =>
      dsimp only
      have hp1 : Pre c f t1 := Pre.of_evaluate h1 hpre
      have hp1' : Pre c f { t1 with clock := min s.clock t1.clock } := hp1
      have hrec : steps (progCompHOL f c2, renameState c f { t1 with clock := min s.clock t1.clock }) =
          steps (c2, { t1 with clock := min s.clock t1.clock }) :=
        ih _ (seq_second_measure_lt c1 c2 s ((none : Option (StackSemResult width)), t1)) c2 _ rfl hp1'
      rw [hrec]
    | some x =>
      dsimp only
  case ite cmp r ri a b =>
    change steps (.ite cmp (findNameSpt f r) (riFindNameHOL f ri) (progCompHOL f a)
      (progCompHOL f b), renameState c f s) = steps (.ite cmp r ri a b, s)
    rw [steps_ite, steps_ite, getVar_findName hf, getVarImm_findName hf]
    rcases hx : getVar r s with _ | x
    · rfl
    · rcases hy : StackSemStateOps.getVarImm (ri.toWordRegImm) s with _ | y
      · rfl
      · dsimp only
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _
        · rfl
        · dsimp only
          rw [ih _ (if_second_measure_lt cmp r ri a b s) b s rfl hpre]
        · dsimp only
          rw [ih _ (if_first_measure_lt cmp r ri a b s) a s rfl hpre]
  case loop body =>
    change steps (.loop (progCompHOL f body), renameState c f s) = steps (.loop body, s)
    rw [steps_loop, steps_loop]
    rcases h1 : evaluate (body, s) with ⟨res, t1⟩
    have hcomp := compCorrect (c := c) (f := f) body s res t1 ⟨h1, hf, hpre⟩
    rw [ih _ (loop_body_measure_lt body s) body s rfl hpre]
    rw [hcomp]
    rw [fixClock_renameState]
    have hfx : fixClock s (res, t1) = (res, { t1 with clock := min s.clock t1.clock }) := rfl
    have hfx2 : (fixClock s (res, t1)).2 = { t1 with clock := min s.clock t1.clock } := rfl
    rw [hfx2, hfx]
    dsimp only
    have hp1 : Pre c f t1 := Pre.of_evaluate h1 hpre
    have hp1' : Pre c f (decClock { t1 with clock := min s.clock t1.clock }) := hp1
    by_cases hc : contLoop res ∧ min s.clock t1.clock ≠ 0
    · split
      · rename_i h
        have hrec : steps (.loop (progCompHOL f body),
            decClock (renameState c f { t1 with clock := min s.clock t1.clock })) =
            steps (.loop body, decClock { t1 with clock := min s.clock t1.clock }) :=
          ih _ (loop_reentry_measure_lt body s (res, t1) hc.2) (.loop body) _ rfl hp1'
        rw [hrec]
      · rename_i h
        exact absurd hc h
    · split
      · rename_i h
        exact absurd h hc
      · rename_i h
        rfl
  case jumpLower r1 r2 dest =>
    change steps (.jumpLower (findNameSpt f r1) (findNameSpt f r2) dest, renameState c f s) =
      steps (.jumpLower r1 r2 dest, s)
    rw [steps_jumpLower, steps_jumpLower, getVar_findName hf, getVar_findName hf]
    rcases hx : getVar r1 s with _ | ⟨x | _⟩
    · rfl
    · rcases hy : getVar r2 s with _ | ⟨y | _⟩
      · rfl
      · dsimp only
        by_cases hw : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower x y = true
        · simp only [if_pos hw]
          have hfc : findCode (.inl dest) (renameState c f s).regs (renameState c f s).code =
              (findCode (.inl dest) s.regs s.code).map (progCompHOL f) :=
            findCode_renameState (dest := .inl dest) hf
          rw [hfc]
          rcases hp : findCode (.inl dest) s.regs s.code with _ | prog
          · simp only [Option.map_none]
          · simp only [Option.map_some]
            by_cases h0 : s.clock = 0
            · split
              · rfl
              · rename_i h; exact absurd h0 h
            · split
              · rename_i h; exact absurd h h0
              · rename_i h
                rw [decClock_renameState]
                rw [ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s h0) prog _ rfl hpre]
        · simp only [if_neg hw]
      · rfl
    · rfl
  case rawCall dest =>
    change steps (.rawCall dest, renameState c f s) = steps (.rawCall dest, s)
    rw [steps_rawCall, steps_rawCall, sptLookup_renameState_code]
    rcases hp : sptLookup dest s.code with _ | prog
    · simp only [Option.map_none]
    · simp only [Option.map_some]
      rcases hd : destSeq prog with _ | ⟨a, body⟩
      · rw [destSeq_progCompHOL, hd]; rfl
      · rw [destSeq_progCompHOL, hd]
        simp only [Option.map_some]
        by_cases h0 : s.clock = 0
        · split
          · rfl
          · rename_i h; exact absurd h0 h
        · split
          · rename_i h; exact absurd h h0
          · rename_i h
            rw [show (Prod.map (progCompHOL f) (progCompHOL f) (a, body)).2 = progCompHOL f body
              from rfl]
            rw [decClock_renameState]
            rw [ih _ (callee_measure_lt body (.rawCall dest) s h0) body _ rfl hpre]
  case call ret dest handler =>
    rcases ret with _ | ⟨retH, link, l1, l2⟩
    · rcases handler with _ | ⟨hp, hl1, hl2⟩
      · change steps (.call none (destFindNameHOL f dest) none, renameState c f s) =
          steps (.call none dest none, s)
        rw [steps_call_none, steps_call_none, findCode_renameState hf]
        rcases hpc : findCode dest s.regs s.code with _ | prog
        · simp only [Option.map_none]
        · simp only [Option.map_some]
          by_cases h0 : s.clock = 0
          · split
            · rfl
            · rename_i h; exact absurd h0 h
          · split
            · rename_i h; exact absurd h h0
            · rename_i h
              rw [decClock_renameState]
              rw [ih _ (callee_measure_lt prog (.call none dest none) s h0) prog _ rfl hpre]
      · change steps (.call none (destFindNameHOL f dest)
          (some (progCompHOL f hp, hl1, hl2)), renameState c f s) =
          steps (.call none dest (some (hp, hl1, hl2)), s)
        rw [steps_call_none_some, steps_call_none_some]
    · rw [progCompHOL_callSome]
      rw [steps_call_some, steps_call_some]
      dsimp only
      have hfc : findCode (destFindNameHOL f dest)
          ((renameState c f s).regs.eraseEq (findNameSpt f link)) (renameState c f s).code =
          (findCode dest (s.regs.eraseEq link) s.code).map (progCompHOL f) := by
        have := findCode_renameState (c := c) (s := { s with regs := s.regs.eraseEq link })
          (dest := dest) hf
        rw [← this]
        show _ = findCode _ (HolFiniteMapExact.mapKeys (findNameSpt f) (s.regs.eraseEq link)) _
        rw [← mapKeys_eraseEq hf.1]; rfl
      rw [hfc]
      rcases hpc : findCode dest (s.regs.eraseEq link) s.code with _ | prog
      · simp only [Option.map_none]
      · simp only [Option.map_some]
        by_cases h0 : s.clock = 0
        · split
          · rfl
          · rename_i h; exact absurd h0 h
        · split
          · rename_i h; exact absurd h h0
          · rename_i h
            rw [← setVar_findName hf, decClock_renameState]
            rcases h1 : evaluate (prog, decClock (setVar link (.loc l1 l2) s)) with ⟨r1', t1⟩
            have hpre' : Pre c f (decClock (setVar link (.loc l1 l2) s)) := hpre
            have hs' : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using h0
            have hpar : stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler)
                (setVar link (.loc l1 l2) s) =
                stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s := by
              simp [stackSemMeasure, setVar]
            have hcallee := callee_measure_lt prog
              (.call (some (retH, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) hs'
            rw [hpar] at hcallee
            rw [ih _ hcallee prog _ rfl hpre']
            have hcomp := compCorrect (c := c) (f := f) prog _ r1' t1 ⟨h1, hf, hpre'⟩
            have hfx : fixClock (decClock (setVar link (.loc l1 l2) s)) (r1', t1) =
                (r1', { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock }) := rfl
            have hfx2 : (fixClock (decClock (setVar link (.loc l1 l2) s)) (r1', t1)).2 =
                { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock } := rfl
            rw [hcomp, fixClock_renameState, hfx2, hfx]
            rcases r1' with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
            · rfl
            · by_cases hx : x = .loc l1 l2
              · simp only [if_pos hx]
                have hp2 : Pre c f t1 := Pre.of_evaluate h1 hpre'
                have hp2' : Pre c f { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock } := hp2
                rw [← hfx2]
                have hrec : steps (progCompHOL f retH, renameState c f
                    (fixClock (decClock (setVar link (.loc l1 l2) s)) (some (StackSemResult.result x), t1)).2) =
                    steps (retH, (fixClock (decClock (setVar link (.loc l1 l2) s)) (some (StackSemResult.result x), t1)).2) :=
                  ih _ (call_continuation_measure_lt retH
                    (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2
                    (some (StackSemResult.result x), t1) h0) retH _ rfl hp2'
                rw [hrec]
              · simp only [if_neg hx]
            · rcases handler with _ | ⟨h, hl1, hl2⟩
              · simp only [handlerComp]
              · simp only [handlerComp]
                by_cases hx : x = .loc hl1 hl2
                · simp only [if_pos hx]
                  have hp2 : Pre c f t1 := Pre.of_evaluate h1 hpre'
                  have hp2' : Pre c f { t1 with clock := min (decClock (setVar link (.loc l1 l2) s)).clock t1.clock } := hp2
                  rw [← hfx2]
                  have hrec : steps (progCompHOL f h, renameState c f
                      (fixClock (decClock (setVar link (.loc l1 l2) s)) (some (StackSemResult.exception x), t1)).2) =
                      steps (h, (fixClock (decClock (setVar link (.loc l1 l2) s)) (some (StackSemResult.exception x), t1)).2) :=
                    ih _ (call_continuation_measure_lt h
                      (.call (some (retH, link, l1, l2)) dest (some (h, hl1, hl2))) s link l1 l2
                      (some (StackSemResult.exception x), t1) h0) h _ rfl hp2'
                  rw [hrec]
                · simp only [if_neg hx]
            all_goals rfl
  all_goals rw [steps_leaf _ _ (by rfl), steps_leaf _ _ (by rfl)]

/-- `stack_names` preserves the StackSem step count exactly. -/
theorem steps_progCompHOL {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} :
    ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      Function.Bijective (findNameSpt f) → Pre c f s →
      steps (progCompHOL f p, renameState c f s) = steps (p, s) :=
  fun p s hf hpre => steps_measure (c := c) (f := f) hf _ p s rfl hpre

/-- `comp_correct` together with the preserved step count. -/
theorem compCorrectWithin {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} :
    ∀ (p : HolProg width) (s : StackSemStateFiniteExact width C F)
      (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F),
      evaluate (p, s) = (r, t) ∧ Function.Bijective (findNameSpt f) ∧
        ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
        s.compile = (fun cfg => c cfg ∘ compileHOL f) →
      evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) ∧
        steps (progCompHOL f p, renameState c f s) = steps (p, s) :=
  fun p s r t ⟨h, hf, ha, hs, hk, hc⟩ =>
    ⟨compCorrect p s r t ⟨h, hf, ha, hs, hk, hc⟩,
      steps_progCompHOL p s hf ⟨ha, hs, hk, hc⟩⟩

/-- The bounded statement implies Flapjack's `comp_correct`. -/
theorem compCorrect_of_within {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (h : evaluate (p, s) = (r, t) ∧ Function.Bijective (findNameSpt f) ∧
      ¬s.useAlloc ∧ ¬s.useStore ∧ ¬s.useStack ∧
      s.compile = (fun cfg => c cfg ∘ compileHOL f)) :
    evaluate (progCompHOL f p, renameState c f s) = (r, renameState c f t) :=
  (compCorrectWithin p s r t h).1

end SteppedFlapjack.StackNamesSteps
