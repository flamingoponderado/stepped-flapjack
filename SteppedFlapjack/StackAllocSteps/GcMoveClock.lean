import SteppedFlapjack.StackAllocSteps.MemcpyCount

/-! Step bounds for simple GC object movement and object-list traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemControl Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A bound valid for every state whose available clock is at most `k`. -/
def ClockBound (k : Nat) (p : HolProg width) (n : Nat) : Prop :=
  ∀ s : StackSemStateFiniteExact width C F, s.clock ≤ k → steps (p, s) ≤ n

theorem clockBoundLeaf (k : Nat) (p : HolProg width) (h : isRecursive p = false) :
    ClockBound (C := C) (F := F) k p 1 := by
  intro s _; exact (steps_leaf p s h).le

theorem clockBoundSeq (k : Nat) (p q : HolProg width) (a b : Nat)
    (hp : ClockBound (C := C) (F := F) k p a)
    (hq : ClockBound (C := C) (F := F) k q b) :
    ClockBound (C := C) (F := F) k (.seq p q) (1 + a + b) := by
  intro s hs
  rw [steps_seq]
  have hfirst := hp s hs
  have hclock := fixClock_clock_le s (evaluate (p,s))
  cases hx : fixClock s (evaluate (p,s)) with
  | mk r t =>
    simp only [hx] at hclock ⊢
    cases r with
    | none => simp only; have hnext := hq t (hclock.trans hs); omega
    | some r => simp only; omega

theorem clockBoundIte (k : Nat) (cmp : Cmp) (r : Nat) (ri : HolRegImm width)
    (p q : HolProg width) (a b : Nat)
    (hp : ClockBound (C := C) (F := F) k p a)
    (hq : ClockBound (C := C) (F := F) k q b) :
    ClockBound (C := C) (F := F) k (.ite cmp r ri p q) (1 + a + b) := by
  intro s hs
  rw [steps_ite]
  have h1 := hp s hs
  have h2 := hq s hs
  split <;> try omega
  split <;> try omega

theorem clockBoundMemcpy (k : Nat) :
    ClockBound (C := C) (F := F) k (Flapjack.Compiler.Backend.StackAlloc.memcpyCode : HolProg width) (12 * (k+1)) := by
  intro s hs
  exact (memcpyStepsLe s).trans (Nat.mul_le_mul_left 12 (by omega))


theorem clockBoundWeaken (k : Nat) (p : HolProg width) (a b : Nat)
    (h : ClockBound (C := C) (F := F) k p a) (hab : a ≤ b) :
    ClockBound (C := C) (F := F) k p b := by
  intro s hs; exact (h s hs).trans hab

open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackAlloc

set_option maxHeartbeats 2000000 in
/-- Object movement has a linear clock bound, including its copy loop. -/
theorem gcMoveClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveCode conf : HolProg width)
      (100 + 12 * (k + 1)) := by
  have h :=
    (clockBoundIte k .test 5 (.imm 1) _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (.skip : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 0 5 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k ((.get 1 .currHeap) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 0 (shiftLength conf) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 0 (wordShiftAmount width) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (addInst 0 1 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (loadInst 1 0 : HolProg width) rfl) (clockBoundIte k .test 1 (.imm 3) _ _ _ _
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 1 2 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 1 (shiftLength conf) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 5 (width - (smallShiftLength conf - 1) - 1) : HolProg width) rfl)
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 5 (width - (smallShiftLength conf - 1) - 1) : HolProg width) rfl))
      (clockBoundLeaf (C := C) (F := F) k (orInst 5 1 : HolProg width) rfl))))
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 1 (width - conf.lenSize) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (add1Inst 1 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 6 1 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 2 0 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 0 1 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundMemcpy (C := C) (F := F) (width := width) k)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 0 6 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 0 (wordShiftAmount width) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (subInst 2 0 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 0 4 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 0 2 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (storeInst 0 2 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (moveHOL 1 4 : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 5 (width - (smallShiftLength conf - 1) - 1) : HolProg width) rfl)
      (clockBoundLeaf (C := C) (F := F) k (rightShiftInst 5 (width - (smallShiftLength conf - 1) - 1) : HolProg width) rfl))
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (leftShiftInst 1 (shiftLength conf) : HolProg width) rfl)
      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (orInst 5 1 : HolProg width) rfl)
      (clockBoundLeaf (C := C) (F := F) k (addInst 4 6 : HolProg width) rfl)))))))))))))))))))))))))
  intro st hs
  have hh := h st hs
  change steps (wordGcMoveCode conf, st) ≤ _ at hh
  omega

theorem clockBoundLoop (k : Nat) (body : HolProg width) (B : Nat)
    (hb : ClockBound (C := C) (F := F) k body B) :
    ClockBound (C := C) (F := F) k (.loop body) ((B + 1) * (k + 1)) := by
  intro s hs
  have h : ∀ n, ∀ u : StackSemStateFiniteExact width C F, u.clock = n → u.clock ≤ k →
      steps (.loop body, u) ≤ (B + 1) * (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hn huk
      rw [steps_loop]
      have hbody := hb u huk
      have hclock := fixClock_clock_le u (evaluate (body, u))
      cases hfix : fixClock u (evaluate (body, u)) with
      | mk r t =>
        simp only [hfix] at hclock ⊢
        split
        · rename_i hcont
          have hlt : (StackSemStateOps.decClock t).clock < n := by
            simp only [StackSemStateOps.decClock]; omega
          have hk : (StackSemStateOps.decClock t).clock ≤ k := by omega
          have hi := ih _ hlt _ rfl hk
          have hmul := Nat.mul_le_mul_left (B + 1)
            (show (StackSemStateOps.decClock t).clock + 1 ≤ n by omega)
          rw [Nat.mul_add, Nat.mul_one]
          omega
        · rw [Nat.mul_add, Nat.mul_one]
          omega
  exact (h s.clock s rfl hs).trans (Nat.mul_le_mul_left (B + 1) (by omega))

set_option maxHeartbeats 2000000 in
/-- Moving a list of objects has a quadratic clock bound. -/
theorem gcMoveListClockBound (k : Nat) (conf : Config) :
    ClockBound (C := C) (F := F) k (wordGcMoveListCode conf : HolProg width)
      ((111 + 12 * (k + 1)) * (k + 1)) := by
  have hbody := clockBoundIte k .notEqual 7 (.imm 0) _ _ _ _

      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (loadInst 5 8 : HolProg width) rfl)

      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (sub1Inst 7 : HolProg width) rfl)

      (clockBoundSeq k _ _ _ _ (gcMoveClockBound (C := C) (F := F) (width := width) k conf)

      (clockBoundSeq k _ _ _ _
      (clockBoundLeaf (C := C) (F := F) k (storeInst 5 8 : HolProg width) rfl)

      (clockBoundLeaf (C := C) (F := F) k (addBytesInWordInst 8 : HolProg width) rfl)))))

      (clockBoundLeaf (C := C) (F := F) k (.break 0 : HolProg width) rfl)
  let body : HolProg width := .ite .notEqual 7 (.imm 0)
    (listSeqHOL [loadInst 5 8, sub1Inst 7, wordGcMoveCode conf, storeInst 5 8, addBytesInWordInst 8]) (.break 0)
  have hb : ClockBound (C := C) (F := F) k body (110 + 12 * (k + 1)) := by
    intro st hs
    have hh := hbody st hs
    change steps (body, st) ≤ _ at hh
    omega
  have hl := clockBoundLoop k _ _ hb
  intro st hs
  have hh := hl st hs
  change steps (wordGcMoveListCode conf, st) ≤ _ at hh
  have heq : 110 + 12 * (k + 1) + 1 = 111 + 12 * (k + 1) := by omega
  rw [heq] at hh
  exact hh

end SteppedFlapjack.StackAllocSteps
