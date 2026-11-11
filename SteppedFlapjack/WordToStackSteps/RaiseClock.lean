import SteppedFlapjack.WordToStackSteps.SequenceZeroClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Raise
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Raise
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- A Word exception is simulated with one additional Stack clock tick. -/
theorem raise_oneClock {width : Nat} [NeZero width] {C F : Type}
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
      ∃ targetPost targetResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + 1}) = (targetResult,targetPost) ∧
        compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  have compiledEq := congrArg Prod.fst compilation
  simp only [compNative] at compiledEq
  subst compiled
  have nameEq : name = 2 := by
    simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
    simpa [callArgConventionHOL] using conventions.2.2
  subst name
  obtain ⟨value,l1,l2,valueEq,jump,resultEq⟩ := sourceRaiseSuccess 2 source sourcePost result execution notError
  obtain ⟨size,nonGc,gc,oldHandler,rest,sourceBound,suffix,postEq⟩ := sourceHandlerFrame source sourcePost l1 l2 jump
  obtain ⟨offset,saved,postRelation,handler,offsetWidth,space,location,savedWord⟩ :=
    fullRaisePostRelation ac k f frame source target lens size nonGc gc oldHandler l1 l2 rest related sourceBound suffix
  have parts : target.useStack = true ∧ target.useStore = true ∧ 4 < k ∧
      sptLookup raiseStubLocation target.code = some (@raiseStubNative width _ false k) := by
    simp only [stateRel] at related
    tauto
  have placed : target.regs.lookup 1 = some value := by
    have placement : ∀ n v, sptLookup n source.locals = some v →
        n % 2 = 0 ∧ if n / 2 < k then target.regs.lookup (n / 2) = some v
        else ((target.stack.drop target.stackSpace).take f)[f - 1 - (n / 2 - k)]? = some v ∧ n / 2 < k + frame := by
      simp only [stateRel,Nat.add_zero] at related
      repeat' (rcases related with ⟨_,related⟩)
      exact related
    have observed := placement 2 value valueEq
    simpa [show 1 < k by omega] using observed.2
  refine ⟨unwindTarget target k offset l1 l2 saved,some (.exception (.loc l1 l2)),?_,?_⟩
  · exact evaluateRaiseCall target k offset l1 l2 saved parts.2.2.2 parts.1 parts.2.1
      handler offsetWidth space location savedWord
  · rw [resultEq]
    simp only [compCorrectResult,Option.map,compileResult,ne_eq,not_true_eq_false,if_false]
    refine ⟨nonGc,gc,?_,?_,?_⟩
    · simpa only [postEq,pushLocals,clearedSource,lastNDrop2] using postRelation
    · simp only [postEq]
    · have distinct : 1 ≠ k := by omega
      simpa [unwindTarget,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,distinct] using placed
end SteppedFlapjack.WordToStackSteps
