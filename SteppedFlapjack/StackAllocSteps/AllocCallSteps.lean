import SteppedFlapjack.StackAllocSteps.AllocCorrectSteps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocCorrect

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open SteppedFlapjack.StackSteps
open Flapjack.Compiler.Backend.StackAlloc.AllocCorrect

/-- The generated collector call adds at most four steps around its GC body. -/
theorem gcStubCallStepBound {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (n m : Nat) (s : StackSemStateFiniteExact width C F)
    (code : List (Nat × HolProg width))
    (hcode : s.code = sptFromAList (compile c code)) :
    steps (.call (some (.skip, 0, n, m)) (.inl gcStubLocation) none, s) ≤
      4 + steps (wordGcCode c, decClock (setVar 0 (.loc n m) s)) := by
  rw [steps_call_some]
  have hfind : findCode (.inl gcStubLocation) (s.regs.eraseEq 0) s.code =
      some (.seq (wordGcCode c) (.ret 0)) := by
    rw [hcode]
    exact Flapjack.Compiler.Backend.StackAlloc.AllocCorrect.findCode_gcStub_compile c _ _
  simp only [hfind]
  split
  · simp only [Nat.add_zero]; omega
  · rw [steps_seq]
    have hret : ∀ t : StackSemStateFiniteExact width C F, steps (.ret 0, t) = 1 := by
      intro t
      exact steps_leaf _ _ rfl
    have hskip : ∀ t : StackSemStateFiniteExact width C F, steps (.skip, t) = 1 := by
      intro t
      exact steps_leaf _ _ rfl
    split <;> split <;> (try simp only [hret, hskip])
    all_goals (try split_ifs) <;> simp +arith

/-- Allocation is simulated by its generated call within an explicit step bound. -/
theorem allocCallCorrectStepsBound {width : Nat} [NeZero width] {C F : Type}
    {c : DataToWord.Config} {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {n' m : Nat} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun c)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl1 : l.lookup 1 = some (.word w)) :
    ∃ ck l2,
      evaluate (.call (some (.skip, 0, n', m)) (.inl gcStubLocation) none, { s with
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
      t.regs.submap l2 ∧
      steps (.call (some (.skip, 0, n', m)) (.inl gcStubLocation) none, { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + ck,
        regs := l, gcFun := anything, code := sptFromAList (compile c (sptToAList s.code)) }) ≤
        4 + allocGcStepCost (width := width) c s.stack.length := by
  have hl0' : (l.updateEq (0, .loc n' m)).lookup 0 = some (.loc n' m) := by
    simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have hl1' : (l.updateEq (0, .loc n' m)).lookup 1 = some (.word w) := by
    simpa [HolFiniteMapExact.updateEq, FUPDATE_HOL] using hl1
  obtain ⟨ck, l2, hev, hhalt, hsub, hret, hsteps⟩ :=
    allocCorrectStepsBound (conf := c) (c := c) (anything := anything)
      ha hr hgc hbl hstack hl0' hl1'
  have htc : t.clock = s.clock :=
    (StackPropsAllocationConstants.allocConst w s t r ha).2.1
  refine ⟨ck + 1, l2, ?_, hsub, ?_⟩
  ·
    rw [evaluate_call]
    simp only [findCode_gcStub_compile]
    rw [if_neg (by simp)]
    have hstate : decClock (setVar 0 (.loc n' m) { s with
          useStore := true, useStack := true, useAlloc := false, clock := s.clock + (ck + 1),
          regs := l, gcFun := anything,
          code := sptFromAList (compile c (sptToAList s.code)) }) =
        { s with
          useStore := true, useStack := true, useAlloc := false, clock := s.clock + ck,
          regs := l.updateEq (0, .loc n' m), gcFun := anything,
          code := sptFromAList (compile c (sptToAList s.code)) } := by
      simp [decClock, setVar]
    rw [hstate, evaluate_seq, hev]
    rcases r with _ | r
    · have h0 := hret rfl
      simp only [StackSemControl.fixClock, htc, show min (s.clock + ck) s.clock = s.clock by omega]
      rw [evaluate_ret]
      simp only [getVar, h0]
      simp [evaluate_skip]
    · have hh := hhalt (by simp)
      simp only [Option.some.injEq] at hh
      subst hh
      simp [StackSemControl.fixClock, htc]
  · have hb := gcStubCallStepBound c n' m
      { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + (ck + 1), regs := l, gcFun := anything,
        code := sptFromAList (compile c (sptToAList s.code)) }
      (sptToAList s.code) rfl
    have hentry : decClock (setVar 0 (.loc n' m) { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + (ck + 1),
        regs := l, gcFun := anything,
        code := sptFromAList (compile c (sptToAList s.code)) }) =
      { s with
        useStore := true, useStack := true, useAlloc := false, clock := s.clock + ck,
        regs := l.updateEq (0, .loc n' m), gcFun := anything,
        code := sptFromAList (compile c (sptToAList s.code)) } := by
      simp [decClock, setVar]
    rw [hentry] at hb
    exact hb.trans (Nat.add_le_add_left hsteps 4)

end SteppedFlapjack.StackAllocSteps
