import SteppedFlapjack.StackAllocSteps.AllocGenFullCorrect
import SteppedFlapjack.StackAllocSteps.CollectorStructural
import SteppedFlapjack.StackSteps.AddClock

/-! A target-step bound for full generational allocation. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend Flapjack.StackSemMeasure
open SteppedFlapjack.StackSteps

/-- Full generational allocation correctness with a concrete target-step bound. -/
theorem allocFullGenStepsBound {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    (hp : ¬wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
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
        loopOnlyCost (2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGcCode conf : HolProg width) := by
  let zero := {s with clock := 0}
  let postzero := {t with clock := 0}
  have hA0 : StackSemAllocation.alloc w zero = (r, postzero) := by
    dsimp [zero, postzero]
    rw [StackPropsAllocationConstants.allocWithClock, ha]
    rfl
  obtain ⟨ck, l2, hck, hrun, hhalt, hsub, hret⟩ :=
    alloc_correct_lemma_Generational_full_bounded (s := zero) (t := postzero)
      hA0 hr hgc hk hbl hstack hl0 hl1 hp
  have hne : r ≠ some .timeOut := by
    intro he
    have hh := hhalt (by rw [he]; simp)
    rw [he] at hh
    cases hh
  have hclock : t.clock = s.clock := by
    have hh := StackSemEvaluateAlloc.alloc_clock_eq w s
    rw [ha] at hh
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
  have hbound := wordGcCodeStructuralBound (C := C) (F := F) (width := width) conf
    (2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) small (by simpa [small, zero] using hck)
  refine ⟨ck, l2, ?_, hhalt, ?_, ?_, ?_⟩
  · simpa [small, zero, post, postzero, hclock, Nat.add_comm] using hadd
  · simpa [postzero] using hsub
  · simpa [postzero] using hret
  · have hboost : steps (wordGcCode conf, {small with clock := small.clock + s.clock}) ≤
        loopOnlyCost (2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) +
          2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) (wordGcCode conf : HolProg width) := by
      rw [hsteps]
      exact hbound
    simpa only [small, zero, Nat.add_comm ck s.clock] using hboost


end SteppedFlapjack.StackAllocSteps
