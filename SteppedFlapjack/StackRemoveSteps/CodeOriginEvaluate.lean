import SteppedFlapjack.StackRemoveSteps.LeafCode
/-! Code provenance for complete evaluator runs. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemMeasure
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}
theorem codeOrigin_mono {a b : Nat} (s t : StackSemStateFiniteExact width C F)
    (h : codeOrigin s t a) (hab : a ≤ b) : codeOrigin s t b := by
  intro label program hl
  rcases h label program hl with hs | ⟨index, hi, name, hm⟩
  · exact Or.inl hs
  · exact Or.inr ⟨index, by omega, name, hm⟩

theorem codeOrigin_trans_effect {a b : Nat} (s middle post : StackSemStateFiniteExact width C F)
    (hfirst : codeOrigin s middle a) (hsecond : codeOrigin middle post b)
    (effect : oracleRunEffect a s middle) : codeOrigin s post (a + b) := by
  obtain ⟨used, hused, horacle, _⟩ := effect
  intro label program h
  rcases hsecond label program h with hm | ⟨index, hi, name, hmem⟩
  · rcases hfirst label program hm with hs | ⟨index, hi, name, hmem⟩
    · exact Or.inl hs
    · exact Or.inr ⟨index, by omega, name, hmem⟩
  · right
    refine ⟨index + used, by omega, name, ?_⟩
    rw [horacle] at hmem
    exact hmem

theorem codeOrigin_leaf (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (leaf : isRecursive p = false) : codeOrigin s t (steps (p, s)) := by
  by_cases hi : ∃ ptr len dptr dlen ret, p = .install ptr len dptr dlen ret
  · obtain ⟨ptr, len, dptr, dlen, ret, rfl⟩ := hi
    rcases codeOrigin_install ptr len dptr dlen ret s t r h with same | installed
    · exact codeOrigin_mono s t same.2 (by rw [steps_leaf _ s leaf]; omega)
    · exact codeOrigin_mono s t installed.2 (by rw [steps_leaf _ s leaf])
  · have hn : ∀ ptr len dptr dlen ret, p ≠ .install ptr len dptr dlen ret := by
      intro ptr len dptr dlen ret heq
      exact hi ⟨ptr, len, dptr, dlen, ret, heq⟩
    exact codeOrigin_same s t _ (leafCode_preserved p s t r h leaf hn)

theorem codeOrigin_evaluate (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t)) :
    codeOrigin s t (steps (p, s)) := by
  by_cases leaf : isRecursive p = false
  · exact codeOrigin_leaf p s t r h leaf
  · cases hp : p <;> rw [hp] at h leaf
    all_goals try (simp [isRecursive] at leaf)
    case seq a b =>
      rcases ha : evaluate (a, s) with ⟨ra, middle⟩
      have ea := oracleRunEffect_evaluate a s middle ra ha
      have ca := codeOrigin_evaluate a s middle ra ha
      rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, ha] at h
      cases ra with
      | none =>
        have smaller := seq_second_measure_lt a b s (evaluate (a, s))
        rw [StackSemEvaluateClock.fixClockEvaluate, ha] at smaller
        have cb := codeOrigin_evaluate b middle t r h
        rw [steps_seq_run a b s middle ha]
        exact codeOrigin_mono _ _ (codeOrigin_trans_effect s middle t ca cb ea) (by omega)
      | some returned =>
        obtain ⟨-, rfl⟩ := h
        rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, ha]
        exact codeOrigin_mono _ _ ca (by omega)
    case ite cmp reg ri a b =>
      cases hx : getVar reg s with
      | none =>
        rw [evaluate_ite] at h; simp only [hx] at h
        obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
      | some x =>
        cases hy : getVarImm (HolRegImm.toWordRegImm ri) s with
        | none =>
          rw [evaluate_ite] at h; simp only [hx, hy] at h
          obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
        | some y =>
          cases hw : wordSemWordCmp cmp x y with
          | none =>
            rw [evaluate_ite] at h; simp only [hx, hy, hw] at h
            obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
          | some truth =>
            cases truth with
            | false =>
              rw [evaluate_ite] at h; simp only [hx, hy, hw] at h
              have cb := codeOrigin_evaluate b s t r h
              rw [steps_ite_false cmp reg ri a b s x y hx hy hw]
              exact codeOrigin_mono _ _ cb (by omega)
            | true =>
              rw [evaluate_ite] at h; simp only [hx, hy, hw] at h
              have ca := codeOrigin_evaluate a s t r h
              rw [steps_ite_true cmp reg ri a b s x y hx hy hw]
              exact codeOrigin_mono _ _ ca (by omega)
    case loop body =>
      rcases hb : evaluate (body, s) with ⟨rb, middle⟩
      have eb := oracleRunEffect_evaluate body s middle rb hb
      have cb := codeOrigin_evaluate body s middle rb hb
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, hb] at h
      dsimp only at h
      split_ifs at h with hc hz
      · obtain ⟨-, rfl⟩ := h
        have ce : codeOrigin middle (emptyEnv middle) 0 := codeOrigin_same _ _ _ rfl
        have ct := codeOrigin_trans_effect s middle (emptyEnv middle) cb ce eb
        rw [steps_loop_exit body s middle rb hb (by simp [hz])]
        exact codeOrigin_mono _ _ ct (by omega)
      · have smaller := loop_reentry_measure_lt body s (evaluate (body, s)) (by
          rw [StackSemEvaluateClock.fixClockEvaluate, hb]; exact hz)
        rw [StackSemEvaluateClock.fixClockEvaluate, hb] at smaller
        have cl := codeOrigin_evaluate (.loop body) (decClock middle) t r h
        have cc : codeOrigin middle (decClock middle) 0 := codeOrigin_same _ _ _ rfl
        have cp := codeOrigin_trans_effect s middle (decClock middle) cb cc eb
        have ep := oracleRunEffect_trans s middle (decClock middle) eb (oracleRunEffect_decClock middle)
        have ct := codeOrigin_trans_effect s (decClock middle) t cp cl ep
        rw [steps_loop_run body s middle rb hb hc hz]
        exact codeOrigin_mono _ _ ct (by omega)
      · obtain ⟨-, rfl⟩ := h
        rw [steps_loop_exit body s _ rb hb (by simp [hc])]
        exact codeOrigin_mono _ _ cb (by omega)
    case rawCall label =>
      cases hf : sptLookup label s.code with
      | none =>
        rw [evaluate_rawCall] at h; simp only [hf] at h
        obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
      | some prog =>
        cases hd : destSeq prog with
        | none =>
          rw [evaluate_rawCall] at h; simp only [hf, hd] at h
          obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
        | some pair =>
          rcases pair with ⟨first, body⟩
          by_cases hz : s.clock = 0
          · rw [evaluate_rawCall] at h; simp only [hf, hd, hz, if_true] at h
            obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
          · rcases he : evaluate (body, decClock s) with ⟨rr, post⟩
            have smaller := callee_measure_lt body (.rawCall label) s hz
            have ep := codeOrigin_evaluate body (decClock s) post rr he
            have e := codeOrigin_trans_effect s (decClock s) post
              (codeOrigin_same _ _ _ rfl) ep (oracleRunEffect_decClock s)
            rw [evaluate_rawCall] at h; simp only [hf, hd, hz, if_false, he] at h
            split_ifs at h <;> obtain ⟨-, rfl⟩ := h
            all_goals rw [steps_rawCall]; simp only [hf, hd, hz, if_false]
            all_goals exact codeOrigin_mono _ _ e (by omega)
    case jumpLower left right label =>
      cases h1 : getVar left s with
      | none =>
        rw [evaluate_jumpLower] at h; simp only [h1] at h
        obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
      | some v1 =>
        cases v1 with
        | loc l o =>
          rw [evaluate_jumpLower] at h; simp only [h1] at h
          obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
        | word x =>
          cases h2 : getVar right s with
          | none =>
            rw [evaluate_jumpLower] at h; simp only [h1, h2] at h
            obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
          | some v2 =>
            cases v2 with
            | loc l o =>
              rw [evaluate_jumpLower] at h; simp only [h1, h2] at h
              obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
            | word y =>
              by_cases hw : wordCmpHOL .lower x y = true
              · cases hf : findCode (.inl label) s.regs s.code with
                | none =>
                  rw [evaluate_jumpLower] at h; simp only [h1, h2, hw, if_true, hf] at h
                  obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
                | some prog =>
                  by_cases hz : s.clock = 0
                  · rw [evaluate_jumpLower] at h; simp only [h1, h2, hw, if_true, hf, hz] at h
                    obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
                  · rcases he : evaluate (prog, decClock s) with ⟨rr, post⟩
                    have smaller := callee_measure_lt prog (.jumpLower left right label) s hz
                    have ep := codeOrigin_evaluate prog (decClock s) post rr he
                    have e := codeOrigin_trans_effect s (decClock s) post
                      (codeOrigin_same _ _ _ rfl) ep (oracleRunEffect_decClock s)
                    rw [evaluate_jumpLower] at h; simp only [h1, h2, hw, if_true, hf, hz, if_false, he] at h
                    split_ifs at h <;> obtain ⟨-, rfl⟩ := h
                    all_goals rw [steps_jumpLower]; simp only [h1, h2, hw, if_true, hf, hz, if_false]
                    all_goals exact codeOrigin_mono _ _ e (by omega)
              · rw [evaluate_jumpLower] at h; simp only [h1, h2, hw] at h
                obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
    case call ret dest handler =>
      cases ret with
      | none =>
        cases hf : findCode dest s.regs s.code with
        | none =>
          rw [evaluate_call] at h; simp only [hf] at h
          obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
        | some prog =>
          cases handler with
          | some hd =>
            rw [evaluate_call] at h; simp only [hf] at h
            obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
          | none =>
            by_cases hz : s.clock = 0
            · rw [evaluate_call] at h; simp only [hf, hz, if_true] at h
              obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
            · rcases he : evaluate (prog, decClock s) with ⟨rr, post⟩
              have smaller := callee_measure_lt prog (.call none dest none) s hz
              have ep := codeOrigin_evaluate prog (decClock s) post rr he
              have e := codeOrigin_trans_effect s (decClock s) post (codeOrigin_same _ _ _ rfl) ep (oracleRunEffect_decClock s)
              rw [evaluate_call] at h; simp only [hf, hz, if_false] at h
              rw [StackSemEvaluateClock.fixClockEvaluate, he] at h
              split_ifs at h <;> obtain ⟨-, rfl⟩ := h
              all_goals rw [steps_call_none]; simp only [hf, hz, if_false]
              all_goals exact codeOrigin_mono _ _ e (by omega)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases hf : findCode dest (s.regs.eraseEq link) s.code with
        | none =>
          rw [evaluate_call] at h; simp only [hf] at h
          obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
        | some prog =>
          by_cases hz : s.clock = 0
          · rw [evaluate_call] at h; simp only [hf, hz, if_true] at h
            obtain ⟨-, rfl⟩ := h; exact codeOrigin_same _ _ _ rfl
          · let start := decClock (setVar link (.loc l1 l2) s)
            rcases he : evaluate (prog, start) with ⟨rr, post⟩
            have hs : codeOrigin s start 0 := codeOrigin_same _ _ _ rfl
            have hsEffect : oracleRunEffect 0 s start := oracleRunEffect_of_fields _ _ _ rfl rfl
            have hs0 : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using hz
            have smaller := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
              (setVar link (.loc l1 l2) s) hs0
            have hpar : stackSemMeasure (.call (some (body, link, l1, l2)) dest handler)
                (setVar link (.loc l1 l2) s) = stackSemMeasure (.call (some (body, link, l1, l2)) dest handler) s := by
              simp [stackSemMeasure, setVar]
            rw [hpar] at smaller
            have hfix := StackSemEvaluateClock.fixClockEvaluate prog start
            rw [he] at hfix
            change fixClock (decClock (setVar link (.loc l1 l2) s)) (rr, post) = (rr, post) at hfix
            have ep := codeOrigin_evaluate prog start post rr he
            have epEffect := oracleRunEffect_evaluate prog start post rr he
            have e := codeOrigin_trans_effect s start post hs ep hsEffect
            have eEffect := oracleRunEffect_trans s start post hsEffect epEffect
            have hbase : steps (prog, start) ≤ steps ((.call (some (body, link, l1, l2)) dest handler : HolProg width), s) := by
              dsimp only [start]
              rw [steps_call_some]
              change evaluate (prog, decClock (setVar link (.loc l1 l2) s)) = (rr, post) at he
              simp only [hf, hz, if_false, he, hfix]
              exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_left _ _)
            rw [evaluate_call] at h; simp only [hf, hz, if_false] at h
            rw [StackSemEvaluateClock.fixClockEvaluate] at h
            change evaluate (prog, decClock (setVar link (.loc l1 l2) s)) = (rr, post) at he
            rw [he] at h
            cases rr with
            | none =>
              dsimp only at h; obtain ⟨-, rfl⟩ := h
              exact codeOrigin_mono _ _ e (by omega)
            | some result =>
              cases result <;> dsimp only at h
              all_goals try (obtain ⟨-, rfl⟩ := h; exact codeOrigin_mono _ _ e (by omega))
              case result value =>
                split_ifs at h with hv
                · obtain ⟨-, rfl⟩ := h; exact codeOrigin_mono _ _ e (by omega)
                · have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
                    s link l1 l2 (evaluate (prog, start)) hz
                  rw [StackSemEvaluateClock.fixClockEvaluate, he] at smaller
                  have ec := codeOrigin_evaluate body post t r h
                  have et := codeOrigin_trans_effect s post t e ec eEffect
                  have hsteps : steps (prog, start) + steps (body, post) ≤
                      steps ((.call (some (body, link, l1, l2)) dest handler : HolProg width), s) := by
                    dsimp only [start]
                    rw [steps_call_some]
                    have hv' : value = .loc l1 l2 := by simpa only [not_not] using hv
                    simp only [hf, hz, if_false, he, hfix]
                    simp only [hv', if_true]
                    exact Nat.le_add_left _ _
                  exact codeOrigin_mono _ _ et (by omega)
              case exception value =>
                cases handler with
                | none =>
                  dsimp only at h; obtain ⟨-, rfl⟩ := h; exact codeOrigin_mono _ _ e (by omega)
                | some entry =>
                  rcases entry with ⟨handlerBody, hl1, hl2⟩
                  dsimp only at h
                  split_ifs at h with hv
                  · obtain ⟨-, rfl⟩ := h; exact codeOrigin_mono _ _ e (by omega)
                  · have smaller := call_continuation_measure_lt handlerBody
                      (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
                      s link l1 l2 (evaluate (prog, start)) hz
                    rw [StackSemEvaluateClock.fixClockEvaluate, he] at smaller
                    have ec := codeOrigin_evaluate handlerBody post t r h
                    have et := codeOrigin_trans_effect s post t e ec eEffect
                    have hsteps : steps (prog, start) + steps (handlerBody, post) ≤
                        steps ((.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)) : HolProg width), s) := by
                      dsimp only [start]
                      rw [steps_call_some]
                      have hv' : value = .loc hl1 hl2 := by simpa only [not_not] using hv
                      simp only [hf, hz, if_false, he, hfix]
                      simp only [hv', if_true]
                      exact Nat.le_add_left _ _
                    exact codeOrigin_mono _ _ et (by omega)

termination_by stackSemMeasure p s
decreasing_by
  all_goals subst p
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, ha] at smaller)
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, hb] at smaller)
  all_goals try (rw [hpar] at smaller)
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, he] at smaller)
  all_goals try (have hh := StackSemEvaluateClock.evaluateClock _ _ _ _ he
                 apply lexNat_of_clock_lt
                 simp only [start, decClock, setVar] at hh ⊢
                 omega)
  all_goals try (apply lexNat_of_clock_lt; simp only [decClock]; omega)
  all_goals first | assumption | exact seq_first_measure_lt _ _ _ | exact if_first_measure_lt _ _ _ _ _ _ | exact if_second_measure_lt _ _ _ _ _ _ | exact loop_body_measure_lt _ _
/-- A source step bound provides a computable bound for every resulting code entry. -/
theorem codeOrigin_computed (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (bounds : BitVec width × BitVec width) (n : Nat) (hsteps : steps (p, s) ≤ n) :
    codeBound (initialBitmapBudget n s) bounds (computedRunCost bounds n p s) t := by
  have hinitial := computedRunCost_bounds bounds n p s
  exact codeOrigin_bound s t (codeOrigin_evaluate p s t r h) hsteps hinitial.2.2.2.1 hinitial.2.2.2.2

end SteppedFlapjack.StackRemoveSteps.CompCorrect
