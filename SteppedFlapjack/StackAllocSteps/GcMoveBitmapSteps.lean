import SteppedFlapjack.StackAllocSteps.GcMoveBitmapClock
import SteppedFlapjack.StackAllocSteps.GcMoveBitmapCorrect
import SteppedFlapjack.StackSteps.AddClock

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- A successful bitmap traversal is bounded by its bitmap value and word width. -/
theorem gcMoveBitmapStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) (w : BitVec width)
    (stack old new stack1 : List (WordLocW width)) (i pa curr i1 pa1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F)
    (hm : wordGcMoveBitmap conf (w, stack, i, pa, curr, s.memory, s.mdomain) =
        some (new, stack1, i1, pa1, m1, true))
    (hcurr : s.store.lookup .currHeap = some (.word curr)) (huse : s.useStore = true)
    (hus : s.useStack = true) (h0 : (s.regs.lookup 0).isSome = true)
    (h1 : (s.regs.lookup 1).isSome = true) (h2 : (s.regs.lookup 2).isSome = true)
    (h3 : s.regs.lookup 3 = some (.word pa)) (h4 : s.regs.lookup 4 = some (.word i))
    (h5 : (s.regs.lookup 5).isSome = true) (h6 : (s.regs.lookup 6).isSome = true)
    (h7 : s.regs.lookup 7 = some (.word w))
    (h8 : s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)))
    (hst : s.stack = init ++ old ++ stack) (hsp : s.stackSpace = init.length)
    (hbound : (width / 8) * s.stack.length < 2 ^ width) :
    let k := w.toNat * (2 ^ width + 1)
    steps (wordGcMoveBitmapCode conf, s) ≤ (120 + 12 * (k + 1)) * (k + 1) := by
  dsimp only
  let k := w.toNat * (2 ^ width + 1)
  by_cases hsmall : s.clock ≤ k
  · exact gcMoveBitmapClockBound k conf s hsmall
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hck, hrun⟩ :=
    gcMoveBitmapBoundedClock hsl hws hw2 hlen hg hshift init w.toNat w rfl
      stack old new stack1 i pa curr i1 pa1 m1 zero hm hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 hst hsp hbound
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (wordGcMoveBitmapCode conf, small) =
      (none, {zero with
        memory := m1
        stack := init ++ old ++ new ++ stack1
        regs := zero.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1), (4, .word i1),
          (5, r5), (6, r6), (7, r7), (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))]}) := by
    simpa [zero, small] using hrun
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure (wordGcMoveBitmapCode conf) small)
    (wordGcMoveBitmapCode conf) small rfl none _ heval (by simp)
  have hsteps : steps (wordGcMoveBitmapCode conf, s) = steps (wordGcMoveBitmapCode conf, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact gcMoveBitmapClockBound k conf small (by simpa [small, k] using hck)

end SteppedFlapjack.StackAllocSteps
