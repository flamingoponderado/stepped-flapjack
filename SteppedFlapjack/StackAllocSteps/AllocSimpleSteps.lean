import SteppedFlapjack.StackAllocSteps.AllocSimpleCorrect
import SteppedFlapjack.StackAllocSteps.AllocSimpleClock
import SteppedFlapjack.StackSteps.AddClock

/-! Simple allocation correctness with a concrete target-step bound. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Extra clock needed by the simple collector for a stack of the given length. -/
def simpleAllocClockBudget (width stackLength : Nat) : Nat :=
  2 ^ width + stackLength * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) +
    2 ^ width * (2 ^ width * (2 ^ width + 1) + 1)

/-- Step cost of the simple collector at a given available clock. -/
def simpleGcStepCost (k : Nat) : Nat :=
  let G := 100 + 12 * (k + 1)
  let R := ((((120 + 12 * (k + 1)) * (k + 1) + 20) * (k + 1)) + 20) * (k + 1)
  let L := ((111 + 12 * (k + 1)) * (k + 1) + 25) * (k + 1)
  73 * (10 + G + R + L)

/-- Simple allocation correctness, with a concrete bound on target steps. -/
theorem allocSimpleStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width} :
    StackSemAllocation.alloc w s = (r, t) ∧ r ≠ some .error ∧
      s.gcFun = wordGcFun conf ∧ conf.gcKind = .simple ∧
      s.bitmaps.length < 2 ^ width - 1 ∧
      s.stack.length * (width / 8) < 2 ^ width ∧
      l.lookup 0 = some ret ∧ l.lookup 1 = some (.word w) →
    ∃ ck l2,
      evaluate (wordGcCode conf, { s with
          useStore := true, useStack := true, useAlloc := false
          clock := s.clock + ck, regs := l, gcFun := anything
          code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true, useStack := true, useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2, gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧ (r = none → l2.lookup 0 = some ret) ∧
      steps (wordGcCode conf, { s with
          useStore := true, useStack := true, useAlloc := false
          clock := s.clock + ck, regs := l, gcFun := anything
          code := sptFromAList (compile c (sptToAList s.code)) }) ≤
        simpleGcStepCost (simpleAllocClockBudget width s.stack.length) := by
  rintro ⟨hA, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
  let zero := {s with clock := 0}
  let postzero := {t with clock := 0}
  have hA0 : StackSemAllocation.alloc w zero = (r, postzero) := by
    dsimp [zero, postzero]
    rw [StackPropsAllocationConstants.allocWithClock, hA]
    rfl
  obtain ⟨ck, l2, hck, hrun, hhalt, hsub, hret⟩ :=
    allocSimpleBoundedClock (s := zero) (t := postzero)
      ⟨hA0, hr, hgc, hk, hbl, hstack, hl0, hl1⟩
  have hne : r ≠ some .timeOut := by
    intro he
    have hh := hhalt (by rw [he]; simp)
    rw [he] at hh
    cases hh
  have hclock : t.clock = s.clock := by
    have hh := StackSemEvaluateAlloc.alloc_clock_eq w s
    rw [hA] at hh
    exact hh
  let small : StackSemStateFiniteExact width C F := {zero with
    useStore := true, useStack := true, useAlloc := false
    clock := ck, regs := l, gcFun := anything
    code := sptFromAList (compile c (sptToAList s.code)) }
  let post : StackSemStateFiniteExact width C F := {postzero with
    useStore := true, useStack := true, useAlloc := false
    code := sptFromAList (compile c (sptToAList s.code))
    regs := l2, gcFun := anything }
  have heval : evaluate (wordGcCode conf, small) = (r, post) := by
    simpa [small, zero, post, postzero] using hrun
  have hadd := StackProps.evaluateAddClock s.clock (wordGcCode conf) small r post ⟨heval, hne⟩
  have hsteps := steps_addClock s.clock (stackSemMeasure (wordGcCode conf) small)
    (wordGcCode conf) small rfl r post heval hne
  have hbound : steps (wordGcCode conf, small) ≤
      simpleGcStepCost (simpleAllocClockBudget width s.stack.length) := by
    apply simpleGcClockBound (simpleAllocClockBudget width s.stack.length) conf hk small
    simpa [small, zero, simpleAllocClockBudget] using hck
  refine ⟨ck, l2, ?_, hhalt, ?_, ?_, ?_⟩
  · simpa [small, zero, post, postzero, hclock, Nat.add_comm] using hadd
  · simpa [postzero] using hsub
  · simpa [postzero] using hret
  · simpa [small, zero, Nat.add_comm] using hsteps ▸ hbound

end SteppedFlapjack.StackAllocSteps
