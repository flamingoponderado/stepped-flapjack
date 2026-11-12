import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import SteppedFlapjack.WordToStackSteps.CallSequenceCost
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.StackSteps

namespace SteppedFlapjack.WordToStackSteps

/-- A Word run within its stack limit has the exact compiled Stack result. -/
theorem compCorrectResult_of_stack_safe {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (targetPost : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (relation : compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens)
    (safe : sourcePost.stackMax.getD (sourcePost.stackLimit+1) ≤ sourcePost.stackLimit) :
    result.map compileResult = targetResult := by
  classical
  unfold compCorrectResult at relation
  split at relation
  · omega
  · rename_i matched
    exact not_not.mp matched

/-- The exact-result case preserves the complete FFI state. -/
theorem compCorrectResult_ffi_of_match {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (targetPost : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (relation : compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens)
    (matched : result.map compileResult = targetResult) : sourcePost.ffi = targetPost.ffi := by
  classical
  unfold compCorrectResult at relation
  rw [if_neg (not_not.mpr matched)] at relation
  have ffi : ∀ {f frame lens extra} {s : WordSemStateFiniteExact width (Nat × C) F},
      stateRel ac k f frame s targetPost lens extra → s.ffi = targetPost.ffi :=
    fun rel => rel.2.2.2.1.symm
  cases result with
  | none => exact ffi relation
  | some r =>
    cases r with
    | result _ values => exact ffi relation.1
    | exception _ value =>
      obtain ⟨nonGc,gc,rel,_,_⟩ := relation
      exact ffi (s := pushLocals nonGc gc sourcePost) rel
    | «break» _ => exact ffi relation
    | «continue» _ => exact ffi relation
    | _ => exact relation.1


end SteppedFlapjack.WordToStackSteps
