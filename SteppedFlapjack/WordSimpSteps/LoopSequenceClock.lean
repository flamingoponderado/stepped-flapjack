import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile
import SteppedFlapjack.WordToStackSteps.NormalizedClock

/-! Clock-based visit bounds for recursive, call-free Word programs. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A call-free Word execution visits at most the program size times the
number of clock ticks consumed plus one. This accounts for nested loops. -/
theorem wordProgram_consumption_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) :
    steps p s ≤ sizeOf p * (s.clock - (evaluate p s).2.clock + 1) := by
  induction shape generalizing s <;> try { rw [steps_leaf _ _ rfl]; apply Nat.mul_pos <;> simp_wf }
  case seq a b ha hb iha ihb =>
    have ha := iha s
    rw [steps_seq, evaluate, fix_clock_evaluate]
    rcases run : evaluate a s with ⟨result,mid⟩
    simp only [run] at ha
    cases result with
    | some r =>
      simp only
      have sz : sizeOf a + 1 ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
      nlinarith
    | none =>
      have hb := ihb mid
      have ca := (evaluate_clock a s none mid run).1
      rcases runb : evaluate b mid with ⟨result,post⟩
      have cb := (evaluate_clock b mid result post runb).1
      simp only [runb] at hb ⊢
      have sz : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf
      have spent : s.clock - mid.clock + (mid.clock - post.clock) = s.clock - post.clock := by omega
      nlinarith
  case ite cmp r ri a b ha hb iha ihb =>
    have sizea : sizeOf a + 1 ≤ sizeOf (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
    have sizeb : sizeOf b + 1 ≤ sizeOf (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp_wf; omega
    rw [steps_ite, evaluate]
    cases hx : getVar r s with
    | none => simp; omega
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp; omega
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]; omega
        | some v =>
          cases v with
          | false =>
            have h := ihb s
            simp only [hv] at ⊢
            nlinarith
          | true =>
            have h := iha s
            simp only [hv] at ⊢
            nlinarith
  case loop names exits body hb ih =>
    induction hc : s.clock using Nat.strongRecOn generalizing s with
    | _ clock rec =>
      have sz : sizeOf body + 1 ≤ 1 + sizeOf names + sizeOf body + sizeOf exits := by omega
      rw [steps_loop, evaluate]
      cases cut : cutState (names,.ln) s with
      | none => simp; nlinarith
      | some entry =>
        obtain ⟨c,_⟩ := cutState_clock_termdep _ _ _ cut
        have entryClock : entry.clock = clock := c.trans hc
        have hbody := ih entry
        simp only [fix_clock_evaluate]
        rcases run : evaluate body entry with ⟨result,post⟩
        have hclock := (evaluate_clock body entry result post run).1
        simp only [run,entryClock] at hbody
        rw [entryClock] at hclock
        have sizeProduct := Nat.mul_le_mul_right (clock - post.clock + 1) sz
        have positive : 1 ≤ clock - post.clock + 1 := by omega
        by_cases cont : wordSemContLoop result = true
        · by_cases hz : post.clock = 0
          · simp only [hz, Nat.sub_zero] at hbody sizeProduct positive
            simp [cont,hz,flushState]
            nlinarith
          · have smaller : (decClock post).clock < s.clock := by simp [decClock]; omega
            have rest := rec _ (by simpa [hc] using smaller) (decClock post) rfl
            rcases hfinal : evaluate (.loop names body exits) (decClock post) with ⟨res,final⟩
            have finalClock := (evaluate_clock (.loop names body exits) (decClock post) res final hfinal).1
            have spent : clock - final.clock = (clock - post.clock) + (post.clock - 1 - final.clock) + 1 := by
              simp only [decClock] at finalClock
              omega
            have sizeEq : sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) =
                1 + sizeOf names + sizeOf body + sizeOf exits := by rfl
            rw [hfinal] at rest
            simp only [decClock, sizeEq] at rest
            simp only [decClock] at hfinal
            simp [cont, hz, wordSemSTOP, decClock, hfinal]
            nlinarith
        · simp only [cont, Bool.false_eq_true, ↓reduceIte, false_and]
          cases result with
          | none => simp [wordSemContLoop] at cont
          | some r =>
            cases r <;> simp only [wordSemExitLoop]
            case «break» n =>
              cases n with
              | zero =>
                cases out : cutState (exits,.ln) post with
                | none => simp; nlinarith
                | some final =>
                  have outClock := cutState_clock_termdep _ _ _ out
                  rcases outClock with ⟨outClock,_⟩
                  simp [outClock]
                  nlinarith
              | succ n => simp; nlinarith
            all_goals simp_wf; nlinarith

/-- A call-free Word execution has a syntax-based bound in the initial clock. -/
theorem wordProgram_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p * (s.clock + 1) := by
  have bound := wordProgram_consumption_bound shape s
  have h := Nat.mul_le_mul_left (sizeOf p) (show s.clock - (evaluate p s).2.clock + 1 ≤ s.clock + 1 by omega)
  exact Nat.le_trans bound h

/-- The existing sequence bound follows from the general recursive bound. -/
theorem loopSequence_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p * (s.clock+1) :=
  wordProgram_clock_bound (loopSequence_program shape) s

end SteppedFlapjack.WordSimpSteps
