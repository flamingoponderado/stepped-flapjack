import SteppedFlapjack.StackRawCallSteps.SeqStandardSteps
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Optimized
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open SteppedFlapjack.StackSteps

/-- The optimized frame-transfer scaffolding costs at most two more steps
than the direct call it replaces. -/
theorem successfulOptimizationSteps {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (space : allocated ≤ s.stackSpace + released) (nonzero : s.clock ≠ 0) :
    steps (optimizedSeq released allocated dest,
      {s with clock := s.clock + (if released < allocated then 1 else 0)}) ≤
      2 + steps (.call none (.inl dest) none, {s with stackSpace := s.stackSpace + released}) := by
  have hfree : ∀ k (st : StackSemStateFiniteExact width C F), steps (.stackFree k, st) = 1 :=
    fun _ _ => steps_leaf _ _ rfl
  have halloc : ∀ k (st : StackSemStateFiniteExact width C F), steps (.stackAlloc k, st) = 1 :=
    fun _ _ => steps_leaf _ _ rfl
  have htick : ∀ st : StackSemStateFiniteExact width C F, steps (.tick, st) = 1 :=
    fun _ => steps_leaf _ _ rfl
  by_cases equal : allocated = released
  · subst allocated
    simp [optimizedSeq, steps_rawCall, steps_call_none, steps_seq,
      StackSemControl.fixClock, decClock, evaluate_stackAlloc, entry, destSeq, findCode,
      useStack, nonzero, halloc, Nat.not_lt_of_ge space]
    simp +arith
  · by_cases less : allocated < released
    · have releaseSafe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeq, equal, less, show ¬ released < allocated by omega,
        steps_rawCall, steps_call_none, steps_seq, StackSemControl.fixClock, decClock,
        evaluate_stackAlloc, evaluate_stackFree, entry, destSeq, findCode,
        useStack, nonzero, releaseSafe, hfree, halloc, finalSpace, Nat.not_lt_of_ge space]
    · have greater : released < allocated := by omega
      have allocateSafe : ¬ s.stackSpace < allocated - released := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace - (allocated - released) := by omega
      simp [optimizedSeq, equal, less, greater, steps_rawCall, steps_call_none, steps_seq,
        StackSemControl.fixClock, decClock, evaluate_stackAlloc, evaluate_tick,
        entry, destSeq, findCode, useStack, allocateSafe, nonzero, halloc, htick, finalSpace, Nat.not_lt_of_ge space]
      simp +arith

/-- A zero-clock optimized transfer costs at most two steps more than its call. -/
theorem zeroOptimizationSteps {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (zero : s.clock = 0) :
    steps (optimizedSeq released allocated dest, s) ≤
      2 + steps (.call none (.inl dest) none, {s with stackSpace := s.stackSpace + released}) := by
  have hfree : ∀ k (st : StackSemStateFiniteExact width C F), steps (.stackFree k, st) = 1 :=
    fun _ _ => steps_leaf _ _ rfl
  have htick : ∀ st : StackSemStateFiniteExact width C F, steps (.tick, st) = 1 :=
    fun _ => steps_leaf _ _ rfl
  by_cases equal : allocated = released
  · subst allocated
    simp [optimizedSeq, steps_rawCall, steps_call_none, entry, destSeq, findCode, zero]
  · by_cases less : allocated < released
    · have safe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeq, equal, less, steps_seq, steps_rawCall, steps_call_none,
        StackSemControl.fixClock, evaluate_stackFree, entry, destSeq, findCode,
        useStack, safe, zero, hfree]
    · simp [optimizedSeq, equal, less, steps_seq, steps_call_none,
        StackSemControl.fixClock, evaluate_tick, entry, findCode, zero, htick, emptyEnv]

/-- An allocation failure in the optimized transfer also fits the same overhead. -/
theorem failedOptimizationSteps {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (failure : s.stackSpace + released < allocated)
    (nonzero : s.clock ≠ 0) :
    steps (optimizedSeq released allocated dest, s) ≤
      2 + steps (.call none (.inl dest) none, {s with stackSpace := s.stackSpace + released}) := by
  have allocationFailure : s.stackSpace < allocated - released := by omega
  have halloc : ∀ k (st : StackSemStateFiniteExact width C F), steps (.stackAlloc k, st) = 1 :=
    fun _ _ => steps_leaf _ _ rfl
  have htick : ∀ st : StackSemStateFiniteExact width C F, steps (.tick, st) = 1 :=
    fun _ => steps_leaf _ _ rfl
  simp [optimizedSeq, show allocated ≠ released by omega, show ¬ allocated < released by omega,
    steps_seq, steps_call_none, StackSemControl.fixClock, evaluate_tick, evaluate_stackAlloc,
    entry, findCode, useStack, failure, allocationFailure, nonzero, halloc, htick, decClock, emptyEnv]

end SteppedFlapjack.StackRawCallSteps
