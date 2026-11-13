import SteppedFlapjack.WordSteps.ClockConsumption
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateDecClock

/-! Normalize clocks to a separately established WordSem step bound. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.WordSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

private theorem normalized_run_of_consumed {C F : Type} (p : WordLangProgHOL (BitVec width))
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (n : Nat)
    (run : evaluate p s = (res, post)) (notTimeout : res ≠ some .timeOut)
    (le : s.clock - post.clock ≤ n) :
    evaluate p {s with clock := n} =
      (res, {post with clock := n - (s.clock - post.clock)}) := by
  have reduced := evaluate_dec_clock p s res post run
  have extended := evaluate_add_clock (n - (s.clock - post.clock)) p
    {s with clock := s.clock - post.clock} res {post with clock := 0} ⟨reduced, notTimeout⟩
  have eqn : s.clock - post.clock + (n - (s.clock - post.clock)) = n := by omega
  simpa only [eqn, Nat.zero_add] using extended

/-- A terminating non-timeout WordSem run can be replayed with any clock at
least its original step count, preserving its result and all non-clock state. -/
theorem loopWord_normalized_run {C F : Type} (p : WordLangProgHOL (BitVec width))
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (n : Nat) (fragment : loopWord p = true) (run : evaluate p s = (res, post))
    (notTimeout : res ≠ some .timeOut) (stepsBound : steps p s ≤ n) :
    evaluate p {s with clock := n} =
      (res, {post with clock := n - (s.clock - post.clock)}) := by
  have cost := loopWord_consumed_le_steps p s fragment
  rw [run] at cost
  exact normalized_run_of_consumed p s post res n run notTimeout (cost.trans stepsBound)

/-- A Word run over a safe function table, including nested calls, can be
replayed with any explicit clock at least its evaluator visit count. -/
theorem tableWord_normalized_run {C F : Type} (p : WordLangProgHOL (BitVec width))
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (n : Nat) (noMt : noMtSubprogsHOL p = true) (noInstall : noInstallSubprogsHOL p = true)
    (tableNoMt : WordProps.noMtCode s.code) (tableNoInstall : WordProps.noInstallCode s.code)
    (run : evaluate p s = (res, post)) (notTimeout : res ≠ some .timeOut)
    (stepsBound : steps p s ≤ n) :
    evaluate p {s with clock := n} =
      (res, {post with clock := n - (s.clock - post.clock)}) := by
  have cost := table_consumption p s noMt noInstall tableNoMt tableNoInstall
  rw [run] at cost
  simp only at cost
  exact normalized_run_of_consumed p s post res n run notTimeout (by omega)

/-- The original compiler state relation survives setting both clocks equally. -/
theorem stateRel_setClocks {C F : Type} (ac : AsmConfigExact width)
    (k f frame : Nat) (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (extra clock : Nat)
    (related : stateRel ac k f frame source target lens extra) :
    stateRel ac k f frame {source with clock := clock} {target with clock := clock} lens extra := by
  unfold stateRel at related ⊢
  exact ⟨rfl, related.2⟩

/-- From a source step bound, replay the same source outcome with a bounded
clock and bound the actual compiled target run on the correspondingly related
state. Semantic correctness of that target run remains a separate obligation. -/
theorem loopWord_normalized_target_bound {C F : Type} (ac : AsmConfigExact width)
    (p : WordLangProgHOL (BitVec width)) (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (n k f frame : Nat) (lens : List Nat) (bs : AppList (BitVec width) × Nat)
    (fragment : loopWord p = true) (run : evaluate p source = (res, post))
    (notTimeout : res ≠ some .timeOut) (stepsBound : steps p source ≤ n)
    (related : stateRel ac k f frame source target lens 0) :
    evaluate p {source with clock := n} =
      (res, {post with clock := n - (source.clock - post.clock)}) ∧
    stateRel ac k f frame {source with clock := n} {target with clock := n} lens 0 ∧
    StackSteps.steps ((compNative ac false p bs (k, f, frame)).1, {target with clock := n}) ≤
      loopOnlyCost n (compNative ac false p bs (k, f, frame)).1 := by
  refine ⟨loopWord_normalized_run p source post res n fragment run notTimeout stepsBound,
    stateRel_setClocks ac k f frame source target lens 0 n related, ?_⟩
  exact loopWord_target_bound ac p fragment bs (k, f, frame) {target with clock := n}

end SteppedFlapjack.WordToStackSteps
