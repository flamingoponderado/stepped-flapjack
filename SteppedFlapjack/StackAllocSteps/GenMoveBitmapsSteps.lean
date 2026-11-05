import SteppedFlapjack.StackAllocSteps.GenMoveBitmapsCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! Step bounds for full and partial generational bitmap-list traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Full generational bitmap-list traversal has a count-based bound. -/
theorem genGcMoveBitmapsStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (d : Nat) (w : BitVec width) (stack old new stack1 : List (WordLocW width))
      (i pa ib pb curr i1 pa1 ib1 pb1 z : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      s.bitmaps.length - (w - 1).toNat = d →
      wordGenGcMoveBitmaps conf (.word w, stack, s.bitmaps, i, pa, ib, pb, curr, s.memory,
        s.mdomain) = some (new, stack1, i1, pa1, ib1, pb1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      s.regs.lookup 0 = some (.word z) → z ≠ 0 →
      (s.regs.lookup 1).isSome = true → (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (.word (w - 1)) →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      steps (wordGenGcMoveBitmapsCode conf, s) ≤ loopOnlyCost (d * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcMoveBitmapsCode conf : HolProg width) := by
  intro d w stack old new stack1 i pa ib pb curr i1 pa1 ib1 pb1 z m1 s hd hm hblen hcurr huse hus h0 hz h1 h2 h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r9, t0, t1, hck, hrun⟩ := genGcMoveBitmapsBoundedClock hsl hws hw2 hlen hg hshift init d w stack old new stack1 i pa ib pb curr i1 pa1 ib1 pb1 z m1 zero hd hm hblen hcurr huse hus h0 hz h1 h2 h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveBitmaps conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Partial generational bitmap-list traversal has a count-based bound. -/
theorem genGcPartialMoveBitmapsStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (d : Nat) (w : BitVec width) (stack old new stack1 : List (WordLocW width))
      (i pa curr i1 pa1 z : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      s.bitmaps.length - (w - 1).toNat = d →
      wordGenGcPartialMoveBitmaps conf (.word w, stack, s.bitmaps, i, pa, curr, s.memory,
        s.mdomain, gs, rs) = some (new, stack1, i1, pa1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      s.regs.lookup 0 = some (.word z) → z ≠ 0 →
      (s.regs.lookup 1).isSome = true → (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (.word (w - 1)) →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      steps (wordGenGcPartialMoveBitmapsCode conf, s) ≤ loopOnlyCost (d * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcPartialMoveBitmapsCode conf : HolProg width) := by
  intro d w stack old new stack1 i pa curr i1 pa1 z m1 s hd hm hblen hcurr huse hus h0 hz h1 h2 h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r9, hck, hrun⟩ := genGcPartialMoveBitmapsBoundedClock hsl hws hw2 hlen hg hshift init d w stack old new stack1 i pa curr i1 pa1 z m1 zero hd hm hblen hcurr huse hus h0 hz h1 h2 h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMoveBitmaps conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh


end SteppedFlapjack.StackAllocSteps
