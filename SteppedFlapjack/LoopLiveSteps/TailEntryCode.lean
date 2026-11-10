import SteppedFlapjack.LoopLiveSteps.TailEntryBound

/-! Loop evaluation preserves its code table, including across nested calls. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- A result cut never changes the Loop code table. -/
theorem cutRes_code (live : NumSet) (res : Option (LoopResultExact width))
    (s : LoopSemStateFiniteExact width F) : (cutRes live (res,s)).2.code = s.code := by
  cases res with
  | some r => rfl
  | none =>
    by_cases h : sptSubsetLive live s.locals <;> by_cases hc : s.clock = 0 <;> simp [cutRes,cutState,h,hc,decClock]

private theorem memStore_code (a : BitVec width) (v : WordLocW width)
    (s t : LoopSemStateFiniteExact width F) (h : memStore a v s = some t) : t.code = s.code := by
  unfold memStore at h
  split at h
  · cases h; rfl
  · contradiction
private theorem loopArith_code (s t : LoopSemStateFiniteExact width F) (op : LoopArith)
    (h : loopArith s op = some t) : t.code = s.code := by
  cases op <;> simp only [LoopSemStateFiniteExact.loopArith] at h <;> repeat' split at h <;> simp_all [LoopSemStateFiniteExact.setVar]
  all_goals first | (subst t; rfl) | (obtain ⟨_,h⟩ := h; subst t; rfl)
private theorem shMemOp_code (op : WordMemOp) (v : Nat) (a : BitVec width)
    (s : LoopSemStateFiniteExact width F) : (shMemOp op v a s).2.code = s.code := by
  cases op <;> simp [shMemOp,shMemLoad,shMemStore,apply_ite,LoopSemStateFiniteExact.callEnv,LoopSemStateFiniteExact.setVar]
  all_goals repeat' first | intro _ | split | rfl

set_option maxHeartbeats 2000000 in
/-- Every Loop evaluation preserves the actual code table. -/
theorem evaluate_code_snd (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    (evaluate p s).2.code = s.code := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → (evaluate p s).2.code = s.code := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
            (evaluate p' s').2.code = s'.code := fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      cases p
      case seq c1 c2 =>
        rw [evaluate,fix_clock_evaluate]
        have h1 := ih c1 s (lexLt (Nat.le_refl _) (by simp +arith))
        split
        · rename_i s1 he
          rw [he] at h1
          exact (ih c2 s1 (lexLt (by have := evaluate_clock _ _ _ _ he; omega) (by simp +arith))).trans h1
        · rename_i r1 s1 _ he; rw [he] at h1; exact h1
      case ite cmp r1 ri c1 c2 live =>
        rw [evaluate]
        split
        · split
          · rw [cutRes_code]; exact ih c1 s (lexLt (Nat.le_refl _) (by simp +arith))
          · rw [cutRes_code]; exact ih c2 s (lexLt (Nat.le_refl _) (by simp +arith))
        · rfl
      case store e v =>
        rw [evaluate]
        repeat' split
        all_goals (try rfl)
        rename_i hms
        exact memStore_code _ _ _ _ hms
      case arith op =>
        rw [evaluate]
        repeat' split
        all_goals (try rfl)
        rename_i hla
        exact loopArith_code _ _ _ hla
      case loop li body lo =>
        rw [evaluate]
        split
        · rename_i s1 hc
          have e1 : s1.code = s.code := by have h := cutRes_code li none s; rw [hc] at h; exact h
          have hs1 := cutRes_none_clock hc
          rw [fix_clock_evaluate, ← e1]
          have hb := ih body s1 (lexLtClock hs1)
          split
          · rename_i s2 he; rw [he] at hb
            exact (ih _ s2 (lexLtClock (Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1))).trans hb
          · rename_i s2 he; rw [he] at hb
            exact (ih _ s2 (lexLtClock (Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1))).trans hb
          · rename_i s2 he; rw [he] at hb; rw [cutRes_code]; exact hb
          · rename_i r s2 _ _ _ he; rw [he] at hb; exact hb
        · rw [cutRes_code]
      case ffi idx p1 l1 p2 l2 cutset =>
        rw [evaluate]
        repeat' split
        all_goals (try rfl)
        all_goals (have hcs := (cutState_some_frame ‹cutState _ _ = some _›).2.2.2.2.2.1)
        all_goals (try (simp only [LoopSemStateFiniteExact.callEnv, hcs]))
      case call ret dest args handler =>
        rw [evaluate]
        split
        · rfl
        rename_i argvals _
        split
        · rfl
        rename_i env prog _
        cases ret with
        | none =>
          simp only
          split
          · rfl
          split
          · rfl
          rename_i hz
          have hp := ih prog { decClock s with locals := env } (lexLtClock (by simp only [decClock]; omega))
          split <;> (rename_i he; rw [he] at hp; exact hp)
        | some nl =>
          obtain ⟨ns, live⟩ := nl
          simp only
          split
          · rfl
          split
          · rename_i s1 hc
            have e1 : s1.code = s.code := by have h := cutRes_code live none s; rw [hc] at h; exact h
            have hs1 := cutRes_none_clock hc
            rw [fix_clock_evaluate, ← e1]
            have hp := ih prog { s1 with locals := env } (lexLtClock hs1)
            split
            · rename_i retvs st1 he
              rw [he] at hp
              have hst1 : st1.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
              split
              · exact hp
              · cases handler with
                | none => exact hp
                | some hd =>
                  obtain ⟨_, _, r, liveOut⟩ := hd
                  simp only; rw [cutRes_code]
                  exact (ih r (setVars ns retvs { st1 with locals := s1.locals })
                    (lexLtClock (by simp only [setVars]; omega))).trans hp
            · rename_i exn st1 he
              rw [he] at hp
              have hst1 : st1.clock < s.clock := Nat.lt_of_le_of_lt (evaluate_clock _ _ _ _ he) hs1
              cases handler with
              | none => exact hp
              | some hd =>
                obtain ⟨n, hp', _, liveOut⟩ := hd
                simp only; rw [cutRes_code]
                exact (ih hp' (setVar n exn { st1 with locals := s1.locals })
                  (lexLtClock (by simp only [setVar]; omega))).trans hp
            · rename_i _ st1 he; rw [he] at hp; exact hp
            · rename_i _ st1 he; rw [he] at hp; exact hp
            · rename_i st1 he; rw [he] at hp; exact hp
            · exact hp
          · rw [cutRes_code]
      case mark q =>
        rw [evaluate]; exact ih q s (lexLt (Nat.le_refl _) (by simp +arith))
      all_goals (try rw [evaluate])
      all_goals (repeat' split)
      all_goals (try dsimp only)
      all_goals (try rfl)
      all_goals (try exact shMemOp_code _ _ _ _)
  exact key _ p s rfl


/-- The code table is unchanged in any completed Loop execution. -/
theorem evaluate_code (p : HolLoopProg width) (s post : LoopSemStateFiniteExact width F)
    (res : Option (LoopResultExact width)) (run : evaluate p s = (res,post)) : post.code = s.code := by
  have h := evaluate_code_snd p s
  rw [run] at h
  exact h

end SteppedFlapjack.LoopLiveSteps
