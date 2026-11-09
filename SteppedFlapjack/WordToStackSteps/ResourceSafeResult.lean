import SteppedFlapjack.WordToStackSteps.DirectTailLinear
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
      result.map compileResult = targetResult ∧
      steps (compiled,{target with clock := limit}) ≤
        directTailLinearCost ac 0 target.code p (bs,n) (k,f,frame) * (limit+1) := by
  obtain ⟨post,stackResult,run,relation,bound⟩ := regTail_bounded_linear ac p shape source sourcePost target result
    k f frame bs bsPost n nPost limit compiled lens noInstall noInstallCode code notTimeout stepBound premises
  have matchResult := compCorrectResult_of_stack_safe ac k f frame {source with clock := limit}
    {sourcePost with clock := limit-(source.clock-sourcePost.clock)} post result stackResult lens relation (by simpa using safe)
  exact ⟨post,stackResult,run,matchResult,bound.trans (directTailLinearCost_le ac limit target.code p (bs,n) (k,f,frame))⟩

end SteppedFlapjack.WordToStackSteps
