import SteppedFlapjack.WordSteps.Defs
import SteppedFlapjack.StackSteps.Defs
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly

/-! Quantitative Word-to-Stack simulation for one-node compilations. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Source constructors that compile directly to one non-recursive node. -/
def basic {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Bool
  | .skip | .tick | .break _ | .continue _ | .ffi _ _ _ _ _ _ => true
  | _ => false

theorem basic_source_steps {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hp : basic p = true) : WordSteps.steps p s = 1 := by
  apply WordSteps.steps_leaf
  cases p <;> simp_all [basic, WordSteps.isRecursive]

theorem basic_compiled_steps {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (target : StackSemStateFiniteExact width C F) (hp : basic p = true) :
    StackSteps.steps ((compNative ac false p bs kf).1, target) = 1 := by
  apply StackSteps.steps_leaf
  cases p <;> simp_all [basic, compNative, StackSteps.isRecursive]

/-- For these compiler cases, semantic correctness comes with an exact target
step count, independent of clocks and all runtime state. -/
theorem basic_simulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (basicProgram : basic program = true)
    (premises : WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := target.clock + extraClock}) =
        WordSteps.steps program source := by
  obtain ⟨extra, post, output, run, related⟩ :=
    CompCorrect.compCorrect ac program source k f frame sourcePost target result
      bs bsPost n nPost compiled lens premises
  refine ⟨extra, post, output, run, related, ?_⟩
  rw [basic_source_steps program source basicProgram]
  have h := basic_compiled_steps ac program (bs, n) (k, f, frame)
    {target with clock := target.clock + extra} basicProgram
  rw [premises.2.2.2.2.2.1] at h
  exact h

end SteppedFlapjack.WordToStackSteps
