import SteppedFlapjack.StackAllocSteps.GenMoveCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! Step bounds for full and partial generational object movement. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend Flapjack.StackSemMeasure
open SteppedFlapjack.StackSteps

/-- Full generational object movement has an initial-clock-independent bound. -/
theorem genGcMoveStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {w : WordLocW width} {i pa ib pb old : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {w1 : WordLocW width} {i1 pa1 ib1 pb1 : BitVec width}
    {m1 : BitVec width → WordLocW width} {s : StackSemStateFiniteExact width C F} :
        wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm) = (w1, i1, pa1, ib1, pb1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
      s.memory = m ∧ s.mdomain = dm ∧
      (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
      (s.regs.lookup 2).isSome = true ∧
      getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧ getVar 5 s = some w ∧
      (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
      s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
      (s.regs.lookup 1).isSome = true ∧ (s.regs.lookup 2).isSome = true ∧
      (s.regs.lookup 6).isSome = true →
    steps (wordGenGcMoveCode conf, s) ≤ loopOnlyCost (2 ^ width) (wordGenGcMoveCode conf : HolProg width) := by
  intro hyp
  let zero := {s with clock := 0}
  have hyp0 :     wordGenGcMove conf (w, i, pa, ib, pb, old, m, dm) = (w1, i1, pa1, ib1, pb1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      zero.store.lookup .currHeap = some (.word old) ∧ zero.useStore = true ∧
      zero.memory = m ∧ zero.mdomain = dm ∧
      (zero.regs.lookup 0).isSome = true ∧ (zero.regs.lookup 1).isSome = true ∧
      (zero.regs.lookup 2).isSome = true ∧
      getVar 3 zero = some (.word pa) ∧ getVar 4 zero = some (.word i) ∧ getVar 5 zero = some w ∧
      (zero.store.lookup (.temp 0)).isSome = true ∧ (zero.store.lookup (.temp 1)).isSome = true ∧
      zero.store.lookup (.temp 2) = some (.word pb) ∧ zero.store.lookup (.temp 3) = some (.word ib) ∧
      (zero.regs.lookup 1).isSome = true ∧ (zero.regs.lookup 2).isSome = true ∧
      (zero.regs.lookup 6).isSome = true := by
    simpa [zero, getVar] using hyp
  obtain ⟨ck, r0, r1, r2, r6, t0, t1, hck, hrun⟩ := genGcMoveBoundedClock hyp0
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMove conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh


/-- Partial generational object movement has an initial-clock-independent bound. -/
theorem genGcPartialMoveStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {w : WordLocW width} {i pa old : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {gs rs : BitVec width} {w1 : WordLocW width} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} {s : StackSemStateFiniteExact width C F} :
        wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
      s.memory = m ∧ s.mdomain = dm ∧ goodDimindex width ∧
      (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
      (s.regs.lookup 2).isSome = true ∧
      getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧ getVar 5 s = some w ∧
      s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
      (s.regs.lookup 1).isSome = true ∧ (s.regs.lookup 2).isSome = true ∧
      (s.regs.lookup 6).isSome = true →
    steps (wordGenGcPartialMoveCode conf, s) ≤ loopOnlyCost (2 ^ width) (wordGenGcPartialMoveCode conf : HolProg width) := by
  intro hyp
  let zero := {s with clock := 0}
  have hyp0 :     wordGenGcPartialMove conf (w, i, pa, old, m, dm, gs, rs) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      zero.store.lookup .currHeap = some (.word old) ∧ zero.useStore = true ∧
      zero.memory = m ∧ zero.mdomain = dm ∧ goodDimindex width ∧
      (zero.regs.lookup 0).isSome = true ∧ (zero.regs.lookup 1).isSome = true ∧
      (zero.regs.lookup 2).isSome = true ∧
      getVar 3 zero = some (.word pa) ∧ getVar 4 zero = some (.word i) ∧ getVar 5 zero = some w ∧
      zero.store.lookup (.temp 0) = some (.word gs) ∧ zero.store.lookup (.temp 1) = some (.word rs) ∧
      (zero.regs.lookup 1).isSome = true ∧ (zero.regs.lookup 2).isSome = true ∧
      (zero.regs.lookup 6).isSome = true := by
    simpa [zero, getVar] using hyp
  obtain ⟨ck, r0, r1, r2, r6, hck, hrun⟩ := genGcPartialMoveBoundedClock hyp0
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMove conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh



end SteppedFlapjack.StackAllocSteps
