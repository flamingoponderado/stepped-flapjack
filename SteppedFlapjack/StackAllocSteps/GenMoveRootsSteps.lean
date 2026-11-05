import SteppedFlapjack.StackAllocSteps.GenMoveRootsCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! Step bounds for full and partial generational root traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Full generational root traversal has a stack-length step bound. -/
theorem genGcMoveRootsStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (stack : List (WordLocW width)), stack.length = n →
    ∀ (old stack1 : List (WordLocW width)) (i pa ib pb curr i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRootsBitmaps conf (stack, s.bitmaps, i, pa, ib, pb, curr, s.memory, s.mdomain) =
        (stack1, i1, pa1, ib1, pb1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (holHd stack) →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      steps (wordGenGcMoveRootsBitmapsCode conf, s) ≤ loopOnlyCost (n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGenGcMoveRootsBitmapsCode conf : HolProg width) := by
  intro n stack hn old stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 s hm hblen hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, t0, t1, hck, hrun, hr9⟩ := genGcMoveRootsBoundedClock hsl hws hw2 hlen hg hshift init n stack hn old stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 zero hm hblen hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveRootsBitmaps conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Partial generational root traversal has a stack-length step bound. -/
theorem genGcPartialMoveRootsStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (stack : List (WordLocW width)), stack.length = n →
    ∀ (old stack1 : List (WordLocW width)) (i pa curr i1 pa1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRootsBitmaps conf (stack, s.bitmaps, i, pa, curr, s.memory, s.mdomain,
        gs, rs) = (stack1, i1, pa1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (holHd stack) →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      steps (wordGenGcPartialMoveRootsBitmapsCode conf, s) ≤ loopOnlyCost (n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGenGcPartialMoveRootsBitmapsCode conf : HolProg width) := by
  intro n stack hn old stack1 i pa curr i1 pa1 m1 s hm hblen hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, hrun, hr9⟩ := genGcPartialMoveRootsBoundedClock hsl hws hw2 hlen hg hshift init n stack hn old stack1 i pa curr i1 pa1 m1 zero hm hblen hcurr huse hus h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMoveRootsBitmaps conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh


end SteppedFlapjack.StackAllocSteps
