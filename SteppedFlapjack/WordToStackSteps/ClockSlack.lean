import SteppedFlapjack.WordToStackSteps.SequenceZeroClock
import SteppedFlapjack.WordToStackSteps.RaiseClock
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
/-! Preserve proved Word-to-Stack simulations with explicit clock slack. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

private theorem targetNoTimeout {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (h : compCorrectResult ac k f frame source sourcePost target result targetResult lens)
    (nonTimeout : result ≠ some .timeOut) : targetResult ≠ some .timeOut := by
  by_cases eq : result.map compileResult = targetResult
  · have hn : result.map compileResult ≠ some .timeOut := by
      clear eq h
      cases result with
      | none => simp
      | some r => cases r <;> simp_all [compileResult]
    intro ht
    exact hn (eq.trans ht)
  · unfold compCorrectResult at h
    rw [if_pos eq] at h
    rw [h.1]
    simp

/-- A non-timeout zero-clock simulation remains valid with explicit target
clock slack; removing that slack recovers the original result relation. -/
theorem zeroSimulation_addSlack {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (sim : ZeroSimulation ac program source)
    (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width) (lens : List Nat)
    (extra : Nat) (notTimeout : result ≠ some .timeOut)
    (premises : WordSemStateFiniteExact.evaluate program source = (result,sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2*frame+2*k) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) = (targetResult,targetPost) ∧
      extra ≤ targetPost.clock ∧
      compCorrectResult ac k f frame source sourcePost {targetPost with clock := targetPost.clock-extra} result targetResult lens := by
  obtain ⟨post,out,run,related⟩ := sim k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have nt := targetNoTimeout ac k f frame source sourcePost post result out lens related notTimeout
  have boosted := Compiler.Backend.StackProps.evaluateAddClock extra compiled target out post ⟨run,nt⟩
  refine ⟨{post with clock := post.clock+extra},out,boosted,by simp,?_⟩
  simpa using related
/-- The one-clock exception simulation also preserves any additional slack. -/
theorem raise_oneClock_addSlack {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ∀ (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
      (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width) (lens : List Nat),
      (WordSemStateFiniteExact.evaluate (.raise name) source = (result, sourcePost) ∧
        result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
        postAllocConventionsHOL k ((.raise name) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.raise name) : WordLangProgHOL (BitVec width)) = true ∧
        compNative ac false (.raise name) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
        (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
        List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
        (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
        maxVarHOL ((.raise name) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) →
      ∀ extra : Nat, ∃ targetPost targetResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + 1 + extra}) = (targetResult,targetPost) ∧
        extra ≤ targetPost.clock ∧
        compCorrectResult ac k f frame source sourcePost {targetPost with clock := targetPost.clock - extra} result targetResult lens := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises extra
  obtain ⟨value,l1,l2,read,jump,resultEq⟩ :=
    Flapjack.WordToStackProofs.CompCorrect.Raise.sourceRaiseSuccess name source sourcePost result premises.1 premises.2.1
  have nt : result ≠ some .timeOut := by rw [resultEq]; simp
  obtain ⟨post,out,run,related⟩ := raise_oneClock ac name source k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have outNt := targetNoTimeout ac k f frame source sourcePost post result out lens related nt
  have boosted := Compiler.Backend.StackProps.evaluateAddClock extra compiled {target with clock := target.clock+1} out post ⟨run,outNt⟩
  refine ⟨{post with clock := post.clock+extra},out,?_,by simp,?_⟩
  · simpa using boosted
  · simpa using related

end SteppedFlapjack.WordToStackSteps
