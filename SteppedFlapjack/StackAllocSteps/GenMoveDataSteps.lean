import SteppedFlapjack.StackAllocSteps.GenMoveDataCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! Fuel-based step bounds for generational data and reference traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Full generational data traversal has a fuel-based step bound. -/
theorem genGcMoveDataStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveData conf k (ha, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      steps (wordGenGcMoveDataCode conf, s) ≤ loopOnlyCost (k * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcMoveDataCode conf : HolProg width) := by
  intro k ha i pa ib pb i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7 h8
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, t0, t1, hck, hrun⟩ := genGcMoveDataBoundedClock hsl hws hw2 hlen hshift old k ha i pa ib pb i2 pa2 ib2 pb2 m2 zero hm hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7 h8
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveData conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Partial generational data traversal has a fuel-based step bound. -/
theorem genGcPartialMoveDataStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old gs rs : BitVec width) :
    ∀ (k : Nat) (ha i pa i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveData conf k (ha, i, pa, old, s.memory, s.mdomain, gs, rs) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) →
      s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      steps (wordGenGcPartialMoveDataCode conf, s) ≤ loopOnlyCost (k * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcPartialMoveDataCode conf : HolProg width) := by
  intro k ha i pa i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hck, hrun⟩ := genGcPartialMoveDataBoundedClock hsl hws hw2 hlen hg hshift old gs rs k ha i pa i2 pa2 m2 zero hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMoveData conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Full generational reference traversal has a fuel-based step bound. -/
theorem genGcMoveRefsStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb ha2 i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRefs conf k (ha, re, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (ha2, i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.store.lookup (.temp 4) = some (.word re) →
      s.regs.lookup 0 = some (.word re) → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      steps (wordGenGcMoveRefsCode conf, s) ≤ loopOnlyCost (k * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcMoveRefsCode conf : HolProg width) := by
  intro k ha i pa ib pb ha2 i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 ht4 h0 h1 h2 h3 h4 h5 h6 h7 h8
  let zero := {s with clock := 0}
  obtain ⟨ck, r1, r2, r5, r6, r7, t0, t1, hck, hrun⟩ := genGcMoveRefsBoundedClock hsl hws hw2 hlen hshift re old k ha i pa ib pb ha2 i2 pa2 ib2 pb2 m2 zero hm hcurr huse ht0 ht1 ht2 ht3 ht4 h0 h1 h2 h3 h4 h5 h6 h7 h8
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveRefs conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Partial generational reference traversal has a fuel-based step bound. -/
theorem genGcPartialMoveRefListStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (pb i pa : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRefList k conf (pb, i, pa, old, s.memory, s.mdomain, c, gs, rs, re) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word pb) →
      s.regs.lookup 9 = some (.word re) →
      steps (wordGenGcPartialMoveRefListCode conf, s) ≤ loopOnlyCost (k * (2 ^ width * (2 ^ width + 1) + 1)) (wordGenGcPartialMoveRefListCode conf : HolProg width) := by
  intro k pb i pa c i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, hrun⟩ := genGcPartialMoveRefListBoundedClock hsl hws hw2 hlen hg hshift re old k pb i pa c i2 pa2 m2 zero hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMoveRefList conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh


end SteppedFlapjack.StackAllocSteps
