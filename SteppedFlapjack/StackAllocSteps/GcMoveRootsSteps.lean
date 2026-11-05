import SteppedFlapjack.StackAllocSteps.GcMoveRootsClock
import SteppedFlapjack.StackAllocSteps.GcMoveRootsCorrect
import SteppedFlapjack.StackSteps.AddClock

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Successful root traversal is bounded by stack length and word width. -/
theorem gcMoveRootsStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init stack old stack1 : List (WordLocW width)) (i pa curr i1 pa1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F)
    (hm : wordGcMoveRootsBitmaps conf (stack, s.bitmaps, i, pa, curr, s.memory, s.mdomain) =
      (stack1, i1, pa1, m1, true)) (hblen : s.bitmaps.length < 2 ^ width - 1)
    (hcurr : s.store.lookup .currHeap = some (.word curr)) (huse : s.useStore = true)
    (hus : s.useStack = true) (h0 : (s.regs.lookup 0).isSome = true)
    (h1 : (s.regs.lookup 1).isSome = true) (h2 : (s.regs.lookup 2).isSome = true)
    (h3 : s.regs.lookup 3 = some (.word pa)) (h4 : s.regs.lookup 4 = some (.word i))
    (h5 : (s.regs.lookup 5).isSome = true) (h6 : (s.regs.lookup 6).isSome = true)
    (h7 : (s.regs.lookup 7).isSome = true)
    (h8 : s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)))
    (h9 : s.regs.lookup 9 = some (holHd stack)) (hst : s.stack = init ++ old ++ stack)
    (hsp : s.stackSpace = init.length) (hbound : (width / 8) * s.stack.length < 2 ^ width) :
    let k := stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)
    steps (wordGcMoveRootsBitmapsCode conf, s) ≤
      (((((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) + 20) * (k + 1)) := by
  dsimp only
  let k := stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)
  by_cases hsmall : s.clock ≤ k
  · exact gcMoveRootsClockBound k conf s hsmall
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, hrun, -⟩ :=
    gcMoveRootsBoundedClock hsl hws hw2 hlen hg hshift init stack.length stack rfl old stack1
      i pa curr i1 pa1 m1 zero hm hblen hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hst hsp hbound
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (wordGcMoveRootsBitmapsCode conf, small) =
      (none, {zero with
        memory := m1
        stack := init ++ old ++ stack1
        regs := zero.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1), (4, .word i1),
          (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)]}) := by
    simpa [zero, small] using hrun
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure (wordGcMoveRootsBitmapsCode conf) small)
    (wordGcMoveRootsBitmapsCode conf) small rfl none _ heval (by simp)
  have hsteps : steps (wordGcMoveRootsBitmapsCode conf, s) = steps (wordGcMoveRootsBitmapsCode conf, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact gcMoveRootsClockBound k conf small (by simpa [small, k] using hck)

end SteppedFlapjack.StackAllocSteps
