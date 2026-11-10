import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import SteppedFlapjack.WordToStackSteps.CallSequenceLinear
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

/-- A safe source run has an exact target result and a linear explicit visit bound. -/
theorem regTail_bounded_linear_safe {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (shape : RegTailShape p) (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode source.code)
    (code : RegTailLocalCode p source.code)
    (notTimeout : result ≠ some .timeOut) (stepBound : WordSteps.steps p source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate p source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false p (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL p < 2 * frame + 2 * k)
    (safe : sourcePost.stackMax.getD (sourcePost.stackLimit+1) ≤ sourcePost.stackLimit) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult,targetPost) ∧
      result.map compileResult = targetResult ∧ sourcePost.ffi = targetPost.ffi ∧
      steps (compiled,{target with clock := limit}) ≤
        callSequenceCost ac 0 target.code p (bs,n) (k,f,frame) * (limit+1) := by
  obtain ⟨post,stackResult,run,relation,bound⟩ := regTail_bounded_local ac p shape source sourcePost target result
    k f frame bs bsPost n nPost limit compiled lens noInstall noInstallCode code notTimeout stepBound premises
  have matchResult := compCorrectResult_of_stack_safe ac k f frame {source with clock := limit}
    {sourcePost with clock := limit-(source.clock-sourcePost.clock)} post result stackResult lens relation (by simpa using safe)
  have ffi := compCorrectResult_ffi_of_match ac k f frame {source with clock := limit}
    {sourcePost with clock := limit-(source.clock-sourcePost.clock)} post result stackResult lens relation matchResult
  exact ⟨post,stackResult,run,matchResult,ffi,bound.trans (callCost_scale ac limit target.code p (bs,n) (k,f,frame))⟩

end SteppedFlapjack.WordToStackSteps
