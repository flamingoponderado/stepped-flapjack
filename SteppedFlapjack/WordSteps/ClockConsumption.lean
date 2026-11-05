import SteppedFlapjack.WordToStackSteps.Loops
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
namespace SteppedFlapjack.WordSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordToStackSteps
variable {width : Nat} [NeZero width] {C F : Type}

theorem const_consumption (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (h : wordProgClockConst p = true) : s.clock ≤ (evaluate p s).2.clock + steps p s := by
  rw [evaluate_const_clock s p h]
  omega

/-- In a call-free loop-fragment run, clock consumption is bounded by the
number of WordSem evaluator invocations, even when loops are nested. -/
theorem loopWord_consumption : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
    loopWord p = true → s.clock ≤ (evaluate p s).2.clock + steps p s := by
  apply evaluate_ind (fun p s => loopWord p = true → s.clock ≤ (evaluate p s).2.clock + steps p s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try { intros; apply const_consumption; rfl }
  case refine_11 =>
    intro s _
    have hs := steps_pos (.tick : WordLangProgHOL (BitVec width)) s
    rw [evaluate]
    split <;> simp only [flushState, decClock] <;> omega
  case refine_12 =>
    intro p s ih hp
    rw [evaluate]
    split
    · simp
    · split
      rename_i res t hrun
      cases res with
      | none => simp
      | some r => cases r <;> simp
  case refine_13 =>
    intro a b s ih hp
    simp only [loopWord, Bool.and_eq_true] at hp
    have ha := ih.2 hp.1
    rw [steps_seq]
    rw [evaluate, fix_clock_evaluate]
    rcases he : evaluate a s with ⟨res, t⟩
    cases res with
    | none =>
      have hb := ih.1 none t ⟨he.symm, rfl⟩ hp.2
      simp only [he] at ha
      simp only
      omega
    | some r =>
      simp only [he] at ha
      simp only
      omega
  case refine_18 =>
    intro cmp r ri a b s ih hp
    simp only [loopWord, Bool.and_eq_true] at hp
    rw [evaluate, steps_ite]
    cases hx : getVar r s with
    | none => simp
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]
        | some v =>
          cases v with
          | false =>
            have hb := ih.2 (some x) (some y) x y false ⟨by simp [hx, hy], rfl, rfl, hv, by simp⟩ hp.2
            simp only [hv]
            omega
          | true =>
            have ha := ih.1 (some x) (some y) x y true ⟨by simp [hx, hy], rfl, rfl, hv, rfl⟩ hp.1
            simp only [hv]
            omega
  case refine_19 =>
    intro names body exitNames s ih hp
    simp only [loopWord] at hp
    rw [steps_loop, evaluate]
    cases hc : cutState (names, .ln) s with
    | none => simp
    | some u =>
      have hcut := cutState_clock_termdep _ _ _ hc
      have hb := ih.2 u hc hp
      simp only [fix_clock_evaluate]
      rcases he : evaluate body u with ⟨res, v⟩
      simp only [he] at hb
      by_cases hcont : wordSemContLoop res = true
      · by_cases hz : v.clock = 0
        · simp [hcont, hz, flushState]
          omega
        · have ht := ih.1 u res v ⟨hc, he.symm, hcont, hz⟩ hp
          dsimp only [wordSemSTOP, decClock] at ht
          simp [hcont, hz, wordSemSTOP, decClock]
          omega
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, false_and]
        cases res with
        | none => simp [wordSemContLoop] at hcont
        | some r =>
          cases r <;> simp only [wordSemExitLoop] <;> try omega
          case «break» k =>
            cases k with
            | zero =>
              cases hout : cutState (exitNames, .ln) v with
              | none => simp; omega
              | some w =>
                have hw := cutState_clock_termdep _ _ _ hout
                change s.clock ≤ w.clock + (1 + (steps body u + 0))
                omega
            | succ n => simp; omega
  case refine_26 =>
    intro ret dest args handler s ih hp
    simp only [loopWord, straightWord, Bool.false_eq_true] at hp
/-- The consumed clock, expressed with natural subtraction, is at most the
actual source step count. -/
theorem loopWord_consumed_le_steps (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (fragment : loopWord p = true) :
    s.clock - (evaluate p s).2.clock ≤ steps p s := by
  have h := loopWord_consumption p s fragment
  omega

end SteppedFlapjack.WordSteps
