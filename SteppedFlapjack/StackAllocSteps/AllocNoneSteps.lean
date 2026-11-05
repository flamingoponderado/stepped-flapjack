import SteppedFlapjack.StackAllocSteps.GcNone
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocNone

/-! No-collector allocation correctness with a 15-step bound. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open SteppedFlapjack.StackSteps

/-- Allocation correctness with a 15-step bound for the no-collector case. -/
theorem allocNoneStepsBound {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width} :
    StackSemAllocation.alloc w s = (r, t) ∧ r ≠ some .error ∧
      s.gcFun = wordGcFun conf ∧ conf.gcKind = .none ∧
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
      t.regs.submap l2 ∧
      (r = none → l2.lookup 0 = some ret) ∧
      steps (wordGcCode conf, { s with
          useStore := true, useStack := true, useAlloc := false
          clock := s.clock + ck, regs := l, gcFun := anything
          code := sptFromAList (compile c (sptToAList s.code)) }) ≤ 15 := by
  intro hyp
  have hk := hyp.2.2.2.1
  obtain ⟨ck, l2, hrun, hhalt, hsub, hret⟩ := alloc_correct_lemma_None hyp
  refine ⟨ck, l2, hrun, hhalt, hsub, hret, ?_⟩
  exact noneGcSteps conf hk _

end SteppedFlapjack.StackAllocSteps
