import SteppedFlapjack.StackAllocSteps.AllocNoneSteps
import SteppedFlapjack.StackAllocSteps.AllocSimpleSteps
import SteppedFlapjack.StackAllocSteps.AllocGenFullSteps
import SteppedFlapjack.StackAllocSteps.AllocGenPartialSteps

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- A concrete allocation-code step bound for each collector configuration. -/
def allocGcStepCost {width : Nat} [NeZero width] (conf : Config) (stackLength : Nat) : Nat :=
  match conf.gcKind with
  | .none => 15
  | .simple => simpleGcStepCost (simpleAllocClockBudget width stackLength)
  | .generational _ =>
      max (loopOnlyCost (2 ^ width + stackLength * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGcCode conf : HolProg width))
          (loopOnlyCost (2 ^ width + (stackLength * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width)))) (wordGcCode conf : HolProg width))

/-- Allocation correctness and a concrete step bound for every collector kind. -/
theorem allocCorrectStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    :
    ∃ ck l2,
      evaluate (wordGcCode conf, { s with
        useStore := true
        useStack := true
        useAlloc := false
        clock := s.clock + ck
        regs := l
        gcFun := anything
        code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true
          useStack := true
          useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2
          gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧ (r = none → l2.lookup 0 = some ret) ∧
      steps (wordGcCode conf, { s with
        useStore := true, useStack := true, useAlloc := false
        clock := s.clock + ck, regs := l, gcFun := anything
        code := sptFromAList (compile c (sptToAList s.code)) }) ≤
        allocGcStepCost (width := width) conf s.stack.length := by
  cases hk : conf.gcKind with
  | none =>
    obtain ⟨ck, l2, he, hh, hs, hr, hb⟩ := allocNoneStepsBound
      ⟨ha, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
    refine ⟨ck, l2, he, hh, hs, hr, ?_⟩
    simpa [allocGcStepCost, hk] using hb
  | simple =>
    obtain ⟨ck, l2, he, hh, hs, hr, hb⟩ := allocSimpleStepsBound
      ⟨ha, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
    refine ⟨ck, l2, he, hh, hs, hr, ?_⟩
    simpa [allocGcStepCost, hk] using hb
  | generational genSizes =>
    by_cases hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store
    · obtain ⟨ck, l2, he, hh, hs, hr, hb⟩ :=
        allocPartialGenStepsBound ha hr hgc hk hbl hstack hl0 hl1 hp
      refine ⟨ck, l2, he, hh, hs, hr, ?_⟩
      rw [allocGcStepCost, hk]
      exact hb.trans (Nat.le_max_right _ _)
    · obtain ⟨ck, l2, he, hh, hs, hr, hb⟩ :=
        allocFullGenStepsBound ha hr hgc hk hbl hstack hl0 hl1 hp
      refine ⟨ck, l2, he, hh, hs, hr, ?_⟩
      rw [allocGcStepCost, hk]
      exact hb.trans (Nat.le_max_left _ _)

end SteppedFlapjack.StackAllocSteps
