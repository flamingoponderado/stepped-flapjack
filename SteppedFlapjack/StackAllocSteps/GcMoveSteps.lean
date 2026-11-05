import SteppedFlapjack.StackAllocSteps.GcMoveClock
import SteppedFlapjack.StackAllocSteps.GcMoveCorrect
import SteppedFlapjack.StackSteps.AddClock

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc
open SteppedFlapjack.StackSteps

/-- The successful object-movement code has a bound independent of initial clock. -/
theorem gcMoveStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {w : WordLocW width} {i pa old : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {w1 : WordLocW width} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} {s : StackSemStateFiniteExact width C F} :
    wordGcMove conf (w, i, pa, old, m, dm) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
      s.memory = m ∧ s.mdomain = dm ∧
      (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
      (s.regs.lookup 2).isSome = true ∧
      getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧ getVar 5 s = some w ∧
      (s.regs.lookup 6).isSome = true →
    steps (wordGcMoveCode conf, s) ≤ 100 + 12 * (2 ^ width + 1) := by
  intro hyp
  by_cases hsmall : s.clock ≤ 2 ^ width
  · exact gcMoveClockBound (2 ^ width) conf s hsmall
  let zero := {s with clock := 0}
  have hyp0 : wordGcMove conf (w, i, pa, old, m, dm) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      zero.store.lookup .currHeap = some (.word old) ∧ zero.useStore = true ∧
      zero.memory = m ∧ zero.mdomain = dm ∧
      (zero.regs.lookup 0).isSome = true ∧ (zero.regs.lookup 1).isSome = true ∧
      (zero.regs.lookup 2).isSome = true ∧
      getVar 3 zero = some (.word pa) ∧ getVar 4 zero = some (.word i) ∧
      getVar 5 zero = some w ∧ (zero.regs.lookup 6).isSome = true := by
    simpa [zero, getVar] using hyp
  obtain ⟨ck, r0, r1, r2, r6, hck, hrun⟩ := gcMoveBoundedClock hyp0
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (wordGcMoveCode conf, small) =
      (none, {zero with memory := m1, regs := zero.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1), (4, .word i1), (5, w1), (6, r6)]}) := by
    simpa [zero, small] using hrun
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure (wordGcMoveCode conf) small)
    (wordGcMoveCode conf) small rfl none _ heval (by simp)
  have hsteps : steps (wordGcMoveCode conf, s) = steps (wordGcMoveCode conf, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact gcMoveClockBound (2 ^ width) conf small (by simpa [small] using hck)

end SteppedFlapjack.StackAllocSteps
