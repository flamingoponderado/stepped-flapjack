import SteppedFlapjack.StackAllocSteps.GcMoveClock
import SteppedFlapjack.StackAllocSteps.GcMoveListCorrect
import SteppedFlapjack.StackSteps.AddClock

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc
open SteppedFlapjack.StackSteps

/-- Successful object-list movement has a bound based on the list length. -/
theorem gcMoveListStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (n : Nat) (a i pa old a1 i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGcMoveList conf (a, BitVec.ofNat width n, i, pa, old, s.memory, s.mdomain) =
        (a1, i1, pa1, m1, true)) (hlt : n < 2 ^ width)
    (hcurr : s.store.lookup .currHeap = some (.word old)) (huse : s.useStore = true)
    (h0 : (s.regs.lookup 0).isSome = true) (h1 : (s.regs.lookup 1).isSome = true)
    (h2 : (s.regs.lookup 2).isSome = true)
    (h3 : s.regs.lookup 3 = some (.word pa)) (h4 : s.regs.lookup 4 = some (.word i))
    (h5 : (s.regs.lookup 5).isSome = true) (h6 : (s.regs.lookup 6).isSome = true)
    (h7 : s.regs.lookup 7 = some (.word (BitVec.ofNat width n)))
    (h8 : s.regs.lookup 8 = some (.word a)) :
    steps (wordGcMoveListCode conf, s) ≤
      (111 + 12 * (n * (2 ^ width + 1) + 1)) * (n * (2 ^ width + 1) + 1) := by
  let k := n * (2 ^ width + 1)
  by_cases hsmall : s.clock ≤ k
  · exact gcMoveListClockBound k conf s hsmall
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, hck, hrun⟩ :=
    gcMoveListBoundedClock hsl hws hw2 hlen hshift n a i pa old a1 i1 pa1 m1 zero
      hm hlt hcurr huse h0 h1 h2 h3 h4 h5 h6 h7 h8
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (wordGcMoveListCode conf, small) =
      (none, {zero with memory := m1, regs := zero.regs.updateListEq [(0, r0), (1, r1), (2, r2),
        (3, .word pa1), (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)]}) := by
    simpa [zero, small] using hrun
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure (wordGcMoveListCode conf) small)
    (wordGcMoveListCode conf) small rfl none _ heval (by simp)
  have hsteps : steps (wordGcMoveListCode conf, s) = steps (wordGcMoveListCode conf, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact gcMoveListClockBound k conf small (by simpa [small, k] using hck)

end SteppedFlapjack.StackAllocSteps
