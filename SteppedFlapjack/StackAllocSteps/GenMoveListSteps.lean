import SteppedFlapjack.StackAllocSteps.GenMoveListCorrect
import SteppedFlapjack.StackAllocSteps.BoundedNormal

/-! Step bounds for full and partial generational object lists. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Full generational object-list traversal is bounded by its length. -/
theorem genGcMoveListStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (n : Nat) (a i pa ib pb old a1 i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveList conf (a, BitVec.ofNat width n, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (a1, i1, pa1, ib1, pb1, m1, true) →
      n < 2 ^ width →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word (BitVec.ofNat width n)) → s.regs.lookup 8 = some (.word a) →
      steps (wordGenGcMoveListCode conf, s) ≤ loopOnlyCost (n * (2 ^ width + 1)) (wordGenGcMoveListCode conf : HolProg width) := by
  intro n a i pa ib pb old a1 i1 pa1 ib1 pb1 m1 s hm hlt hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7 h8
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, t0, t1, hck, hrun⟩ := genGcMoveListBoundedClock hsl hws hw2 hlen hshift n a i pa ib pb old a1 i1 pa1 ib1 pb1 m1 zero hm hlt hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7 h8
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenMoveList conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

/-- Partial generational object-list traversal is bounded by its length. -/
theorem genGcPartialMoveListStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (n : Nat) (a i pa old a1 i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveList conf (a, BitVec.ofNat width n, i, pa, old, s.memory, s.mdomain,
        gs, rs) = (a1, i1, pa1, m1, true) →
      n < 2 ^ width →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word (BitVec.ofNat width n)) → s.regs.lookup 8 = some (.word a) →
      steps (wordGenGcPartialMoveListCode conf, s) ≤ loopOnlyCost (n * (2 ^ width + 1)) (wordGenGcPartialMoveListCode conf : HolProg width) := by
  intro n a i pa old a1 i1 pa1 m1 s hm hlt hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8
  let zero := {s with clock := 0}
  obtain ⟨ck, r0, r1, r2, r5, r6, hck, hrun⟩ := genGcPartialMoveListBoundedClock hsl hws hw2 hlen hg hshift n a i pa old a1 i1 pa1 m1 zero hm hlt hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8
  apply stepsOfBoundedNormalRun _ _ _ _ (loopOnlyCostBound _ _ (loopOnlyGenPartialMoveList conf))
  refine ⟨ck, hck, ?_⟩
  have hh := congrArg Prod.fst hrun
  simpa [zero] using hh

end SteppedFlapjack.StackAllocSteps
