import SteppedFlapjack.StackAllocSteps.GcMoveLoopCorrect
import SteppedFlapjack.StackAllocSteps.GcMoveLoopClock
import SteppedFlapjack.StackSteps.AddClock

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc
open SteppedFlapjack.StackSteps

/-- A successful heap traversal is bounded in terms of its fuel and word width. -/
theorem gcMoveLoopStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (fuel : Nat) (pb i pa old : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
    (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F)
    (hm : wordGcMoveLoop fuel conf (pb, i, pa, old, s.memory, s.mdomain, c) = (i2, pa2, m2, true))
    (hcurr : s.store.lookup .currHeap = some (.word old)) (huse : s.useStore = true)
    (h0 : (s.regs.lookup 0).isSome = true) (h1 : (s.regs.lookup 1).isSome = true)
    (h2 : (s.regs.lookup 2).isSome = true)
    (h3 : s.regs.lookup 3 = some (.word pa)) (h4 : s.regs.lookup 4 = some (.word i))
    (h5 : (s.regs.lookup 5).isSome = true) (h6 : (s.regs.lookup 6).isSome = true)
    (h7 : (s.regs.lookup 7).isSome = true) (h8 : s.regs.lookup 8 = some (.word pb)) (hc : c = true) :
    let k := fuel * (2 ^ width * (2 ^ width + 1) + 1)
    steps (wordGcMoveLoopCode conf, s) ≤ (((111 + 12 * (k + 1)) * (k + 1) + 25) * (k + 1)) := by
  dsimp only
  let k := fuel * (2 ^ width * (2 ^ width + 1) + 1)
  by_cases hsmall : s.clock ≤ k
  · exact gcMoveLoopClockBound k conf s hsmall
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hck, hrun⟩ :=
    gcMoveLoopBoundedClock hsl hws hw2 hlen hshift fuel pb i pa old c i2 pa2 m2 zero
      hm hcurr huse h0 h1 h2 h3 h4 h5 h6 h7 h8 hc
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (wordGcMoveLoopCode conf, small) =
      (none, {zero with memory := m2, regs := zero.regs.updateListEq [(0, r0), (1, r1), (2, r2),
        (3, .word pa2), (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)]}) := by
    simpa [zero, small] using hrun
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure (wordGcMoveLoopCode conf) small)
    (wordGcMoveLoopCode conf) small rfl none _ heval (by simp)
  have hsteps : steps (wordGcMoveLoopCode conf, s) = steps (wordGcMoveLoopCode conf, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact gcMoveLoopClockBound k conf small (by simpa [small, k] using hck)

end SteppedFlapjack.StackAllocSteps
