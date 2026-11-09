import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile
import SteppedFlapjack.WordToStackSteps.NormalizedClock

/-! Clock-based visit bounds for recursive, call-free Word programs. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Executable count of control nodes, independent of literal values. -/
def wordControlWeight : WordLangProgHOL (BitVec width) → Nat
  | .seq a b | .ite _ _ _ a b => 1 + wordControlWeight a + wordControlWeight b
  | .loop _ body _ => 1 + wordControlWeight body
  | _ => 1
theorem wordControl_consumption_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) :
    steps p s ≤ wordControlWeight p * (s.clock - (evaluate p s).2.clock + 1) := by
  induction shape generalizing s <;> try { rw [steps_leaf _ _ rfl]; apply Nat.mul_pos <;> simp [wordControlWeight] }
  case seq a b ha hb iha ihb =>
    have ha := iha s
    rw [steps_seq, evaluate, fix_clock_evaluate]
    rcases run : evaluate a s with ⟨result,mid⟩
    simp only [run] at ha
    cases result with
    | some r =>
      simp only
      have sz : wordControlWeight a + 1 ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
      nlinarith
    | none =>
      have hb := ihb mid
      have ca := (evaluate_clock a s none mid run).1
      rcases runb : evaluate b mid with ⟨result,post⟩
      have cb := (evaluate_clock b mid result post runb).1
      simp only [runb] at hb ⊢
      have sz : 1 + wordControlWeight a + wordControlWeight b ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]
      have spent : s.clock - mid.clock + (mid.clock - post.clock) = s.clock - post.clock := by omega
      nlinarith
  case ite cmp r ri a b ha hb iha ihb =>
    have sizea : wordControlWeight a + 1 ≤ wordControlWeight (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
    have sizeb : wordControlWeight b + 1 ≤ wordControlWeight (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
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
      simp only [wordControlWeight]
      have sz : wordControlWeight body + 1 ≤ 1 + wordControlWeight body := by omega
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
            have sizeEq : wordControlWeight (.loop names body exits : WordLangProgHOL (BitVec width)) =
                1 + wordControlWeight body := by rfl
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
            all_goals simp; nlinarith


theorem wordControl_le_size {p : WordLangProgHOL (BitVec width)} (shape : Program p) :
    wordControlWeight p ≤ sizeOf p := by
  induction shape <;> simp_all [wordControlWeight] <;> omega

/-- The executable control-node count bounds visits using the initial clock. -/
theorem wordControl_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ wordControlWeight p * (s.clock + 1) := by
  have bound := wordControl_consumption_bound shape s
  exact bound.trans (Nat.mul_le_mul_left _ (by omega))

/-- The control-node bound implies the earlier size-based consumption bound. -/
theorem wordProgram_consumption_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) :
    steps p s ≤ sizeOf p * (s.clock - (evaluate p s).2.clock + 1) :=
  (wordControl_consumption_bound shape s).trans
    (Nat.mul_le_mul_right _ (wordControl_le_size shape))

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
