import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock

/-!
# Removing clock from a LabSem run

Flapjack's `LabProps.evaluateAddClock` adds clock to a run that does not time
out. `evaluate_subClock` removes it: a run that ends with more clock than is
removed ends the same way, with that much less clock. Such a run did not time
out, since a timed-out run ends with zero clock. The removed clock must be
strictly less than the final clock because `Halt` and final FFI outcomes need
a nonzero clock but do not consume it.

The proof combines `evaluateAddClock` with two facts proved by induction on
the evaluator: the clock never increases (`evaluate_clock_le`), and a run that
times out stops in a zero-clock state that a run with more clock passes through
(`evaluate_timeOut_addClock`).

This is stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps

section
variable {width : Nat} [NeZero width] {C F : Type}

private theorem clockAddSub {clock extra : Nat} (hne : clock ≠ 0) :
    clock + extra - 1 = clock - 1 + extra := by omega

private theorem asmInst_clock (i : HolInst width) (s : State width C F) :
    (asmInst i s).clock = s.clock := (asmInstConsts i s).2.2.1

/-- A final shared-memory outcome leaves the state unchanged. -/
theorem shareMemOp_final_state (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (state next : State width C F) (outcome : HolFinalEvent)
    (h : shareMemOp operator register address state = some (.final outcome, next)) :
    next = state := by
  cases operator <;> simp only [shareMemOp, shareMemLoad, shareMemStore] at h
  all_goals repeat' first | split at h | simp_all
  all_goals exact h.2.symm

/-- The clock of a LabSem run never increases. -/
theorem evaluate_clock_le (s : State width C F) : (evaluate s).2.clock ≤ s.clock := by
  fun_induction evaluate s
  all_goals try (simp only; omega)
  case case11 hshare =>
    simp only [shareMemOp_final_state _ _ _ _ _ _ hshare]; omega
  case case27 ih =>
    split
    · rename_i heq1 heq2
      simp only [heq1, Option.some.injEq, Prod.mk.injEq, List.cons.injEq,
        Compiler.Backend.LabLang.Section.mk.injEq] at *
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq2
      split
      · exact Nat.le_trans ih (Nat.sub_le _ _)
      · simp
    · simp
  case case28 hv _ _ =>
    split
    · rename_i heq1 heq2
      simp only [heq1, Option.some.injEq, Prod.mk.injEq, List.cons.injEq,
        Compiler.Backend.LabLang.Section.mk.injEq] at *
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq2
      obtain ⟨rfl, rfl⟩ := ‹_ ∧ _›
      rw [if_neg hv]
      exact Nat.le_refl _
    · simp
  all_goals rename_i ih
  all_goals refine Nat.le_trans ih ?_
  all_goals simp_all +zetaDelta [incPc, decClock, updPc, updReg, asmInstConsts]
  all_goals omega

/-- A run that times out stops in a zero-clock state. -/
theorem evaluate_timeOut_clock (s : State width C F) :
    (evaluate s).1 = .timeOut → (evaluate s).2.clock = 0 := by
  fun_induction evaluate s
  all_goals intro hresult
  all_goals try contradiction
  all_goals simp_all +zetaDelta
  all_goals split at hresult <;> simp_all

/-- A run that times out passes, with `extra` more clock, through its final
state with `extra` more clock. -/
theorem evaluate_timeOut_addClock (s : State width C F) (extra : Nat) :
    (evaluate s).1 = .timeOut →
    evaluate { s with clock := s.clock + extra } =
      evaluate { (evaluate s).2 with clock := (evaluate s).2.clock + extra } := by
  fun_induction evaluate s
  all_goals intro hresult
  all_goals try contradiction
  all_goals try rfl
  all_goals conv => lhs; rw [evaluate]
  case case12 s h op reg addr _ _ hf ffi bytes next hs hnextClock ih =>
    have hc := (shareMemOpAddClockSame s op reg addr extra ffi bytes next
      { name := .sharedMem .mappedRead, configuration := [], bytes := [],
          outcome := .failed } s).2.1 ⟨h, hs⟩
    rw [Nat.add_comm extra s.clock] at hc
    simp only [asmFetch] at hf
    simp only [Nat.add_eq_zero_iff, h, false_and, ↓reduceIte, asmFetch, hf]
    rw [hc]
    simpa only [Nat.add_comm] using ih hresult
  all_goals simp_all +zetaDelta [clockAddSub, asmInst_clock, Nat.add_eq_zero_iff, asmFetch,
    asmInstWithClock, getPcValue, getRetLoc, regImm, incPc, decClock, updPc, updReg]
  all_goals split at hresult <;> simp_all

/-- Removing clock from a LabSem run: a run from clock `c + d` that ends with
more than `d` clock (so it did not time out) runs the same way from clock `c`,
ending with `d` less clock. -/
theorem evaluate_subClock (t : State width C F) (c d : Nat) (res : MachineResult)
    (t2 : State width C F) (h : evaluate { t with clock := c + d } = (res, t2))
    (hd : d < t2.clock) :
    evaluate { t with clock := c } = (res, { t2 with clock := t2.clock - d }) := by
  rcases e : evaluate { t with clock := c } with ⟨r0, u⟩
  by_cases hto : r0 = .timeOut
  · have hq := evaluate_timeOut_addClock { t with clock := c } d (by rw [e]; exact hto)
    have hz := evaluate_timeOut_clock { t with clock := c } (by rw [e]; exact hto)
    rw [e] at hq hz
    simp only at hq hz
    have hle := evaluate_clock_le { u with clock := u.clock + d }
    rw [← hq, h] at hle
    simp only at hle
    omega
  · have hadd := evaluateAddClock { t with clock := c } r0 u d ⟨e, hto⟩
    simp only at hadd
    rw [h] at hadd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hadd
    simp

/-- `evaluate_subClock` with the clock to keep given as a bound: a run from
clock `c` that ends with clock `e` runs the same way from
any clock `m` with `c - e < m ≤ c`. -/
theorem evaluate_lowerClock (t : State width C F) (m : Nat) (res : MachineResult)
    (t2 : State width C F) (h : evaluate t = (res, t2))
    (hm : t.clock < m + t2.clock) (hmc : m ≤ t.clock) :
    evaluate { t with clock := m } = (res, { t2 with clock := t2.clock - (t.clock - m) }) := by
  apply evaluate_subClock t m (t.clock - m) res t2 _ (by omega)
  rw [show m + (t.clock - m) = t.clock by omega]
  exact h

end

end SteppedFlapjack.StackToLabSteps
