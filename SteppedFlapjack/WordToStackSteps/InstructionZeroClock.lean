import SteppedFlapjack.WordToStackSteps.NormalizedClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.InstSimulation

/-! A zero-extra-clock simulation for WordSem machine instructions. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackRemoveSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

private theorem instConventionCodec (i : WordLangInst (BitVec width)) :
    instArgConvention i = instArgConventionExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | ⟨_, _⟩ | ⟨a⟩ | ⟨_, _, _⟩ | ⟨_⟩
  all_goals try rfl
  rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  all_goals (cases ri <;> rfl)

/-- A compiled instruction preserves the original semantic relation with no
additional target clock, while satisfying its structural runtime bound. -/
theorem inst_zeroClock {C F : Type} (ac : AsmConfigExact width)
    (i : WordLangInst (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.inst i) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.inst i) = true ∧ flatExpConventions (.inst i) = true ∧
      compNative ac false (.inst i) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.inst i) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, target) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      StackSteps.steps (compiled, target) ≤ loopOnlyCost 0 compiled := by
  rcases premises with ⟨execution, notError, related, conventions, _flat,
    compilation, _lengthBound, _bitmapBound, _bitmapPrefix, _labels, maxBound⟩
  have shape := straightLine_compileInst ac i (bs, n) (k, f, frame)
  rw [compilation] at shape
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases instRun : WordSemStateFiniteExact.inst i source with _ | post
  · rw [instRun] at execution
    obtain ⟨rfl, -⟩ := Prod.mk.inj execution
    exact absurd rfl notError
  · rw [instRun] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    have conventionParts := conventions
    simp only [postAllocConventionsHOL, everyVarHOL, callArgConventionHOL,
      Bool.and_eq_true] at conventionParts
    obtain ⟨physical, _, convention⟩ := conventionParts
    simp only [compNative, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -⟩ := compilation
    obtain ⟨post', run, postRel, _, _⟩ :=
      InstSimulation.evaluateWInst ac (HolInst.ofWordLangInst i) k f frame source post
        target lens (by simpa only [HolInst.to_of] using instRun)
        (by simpa only [HolInst.to_of] using physical)
        (by simpa only [HolInst.to_of, maxVarHOL] using maxBound)
        (by rw [← instConventionCodec]; exact convention) related
    refine ⟨post', none, run, ?_, straightLineSteps _ shape target⟩
    simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, if_false]
    exact postRel


/-- A source-step bound supplies the clock for an outcome-preserving compiled
instruction execution, with no additional target clock. -/
theorem inst_normalized_simulation {C F : Type} (ac : AsmConfigExact width)
    (i : WordLangInst (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (notTimeout : result ≠ some .timeOut) (stepsBound : WordSteps.steps (.inst i) source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate (.inst i) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.inst i) = true ∧ flatExpConventions (.inst i) = true ∧
      compNative ac false (.inst i) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.inst i) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
        targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := limit}) ≤ loopOnlyCost 0 compiled := by
  have normalized := loopWord_normalized_run (.inst i) source sourcePost result limit rfl
    premises.1 notTimeout stepsBound
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  apply inst_zeroClock ac i {source with clock := limit}
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result k f frame bs bsPost n nPost compiled lens
  exact ⟨normalized, premises.2.1, related, premises.2.2.2⟩

end SteppedFlapjack.WordToStackSteps
