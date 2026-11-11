import SteppedFlapjack.WordToStackSteps.ReturningHandlerComplete
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

/-! Zero-clock simulations compose across sequences containing calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang

/-- A sequence of loop blocks and calls into loop-block code. -/
inductive CallSequence {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | block {p} : LoopBlock p → CallSequence p
  | tail (dest args) : CallSequence (.call none dest args none)
  | returning (values names retCode l1 l2 dest args) :
      LoopBlock retCode → CallSequence (.call (some (values,names,retCode,l1,l2)) dest args none)
  | handler (values names retCode l1 l2 dest args var handlerCode h1 h2) :
      LoopBlock retCode → LoopBlock handlerCode →
      CallSequence (.call (some (values,names,retCode,l1,l2)) dest args (some (var,handlerCode,h1,h2)))
  | seq {a b} : CallSequence a → CallSequence b → CallSequence (.seq a b)

/-- The whole sequence has a zero-extra-clock simulation. Code shape is
preserved across each component by the original no-install theorem. -/
theorem callSequence_zero {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) {p : WordLangProgHOL (BitVec width)} (shape : CallSequence p) :
    ∀ (source : WordSemStateFiniteExact width (Nat × C) F),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode source.code →
      (∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q) →
      ZeroSimulation ac p source := by
  induction shape with
  | block block =>
    intro source noInstall noInstallCode code
    exact loopBlock_zero ac _ source block
  | tail dest args =>
    intro source noInstall noInstallCode code
    exact tailCall_zero_of_code ac dest args source code
  | returning values names retCode l1 l2 dest args retBlock =>
    intro source noInstall noInstallCode code
    exact zeroReturningNone ac values names retCode l1 l2 dest args source
      (fun t _ _ => loopBlock_zero ac retCode t retBlock)
      (fun loc arity p lookup t _ _ => loopBlock_zero ac p t (code loc arity p lookup))
  | handler values names retCode l1 l2 dest args var handlerCode h1 h2 retBlock handlerBlock =>
    intro source noInstall noInstallCode code
    exact zeroReturningHandlerCase ac values names retCode l1 l2 dest args var h1 h2 handlerCode source
      (fun t _ _ => loopBlock_zero ac retCode t retBlock)
      (fun t _ _ => loopBlock_zero ac handlerCode t handlerBlock)
      (fun loc arity p lookup t _ _ => loopBlock_zero ac p t (code loc arity p lookup))
  | @seq a b ha hb iha ihb =>
    intro source noInstall noInstallCode code
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at noInstall
    apply zeroSeq ac a b source (iha source noInstall.1 noInstallCode code)
    intro result middle run
    have eq : middle.code = source.code := by
      have preserved := WordSemStateFiniteExact.code_evaluate a source noInstall.1 noInstallCode
      rw [← run.1] at preserved
      exact preserved
    apply ihb middle noInstall.2
    · simpa only [eq] using noInstallCode
    · simpa only [eq] using code


/-- The sequence consumes at most its actual number of source evaluator steps. -/
theorem callSequence_consumed {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) {p : WordLangProgHOL (BitVec width)} (shape : CallSequence p) :
    ∀ (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
      (result : Option (WordSemResult width)),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode source.code →
      (∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q) →
      WordSemStateFiniteExact.evaluate p source = (result,sourcePost) →
      result ≠ some .error → result ≠ some .timeOut →
      source.clock - sourcePost.clock ≤ WordSteps.steps p source := by
  induction shape with
  | block block =>
    intro source sourcePost result noInstall noInstallCode code run notError notTimeout
    have bound := WordSteps.loopWord_consumption _ source (loopBlock_loop block)
    rw [run] at bound
    simp only at bound
    omega
  | tail dest args =>
    intro source sourcePost result noInstall noInstallCode code run notError notTimeout
    exact tailCall_consumed dest args source sourcePost result code run notError notTimeout
  | returning values names retCode l1 l2 dest args retBlock =>
    intro source sourcePost result noInstall noInstallCode code run notError notTimeout
    exact returningNone_consumed (C := C) (F := F) ac values names retCode l1 l2 dest args source sourcePost result retBlock code run notError notTimeout
  | handler values names retCode l1 l2 dest args var handlerCode h1 h2 retBlock handlerBlock =>
    intro source sourcePost result noInstall noInstallCode code run notError notTimeout
    exact returningHandler_consumed (C := C) (F := F) ac values names retCode l1 l2 dest args var h1 h2 handlerCode source sourcePost result retBlock handlerBlock code run notError notTimeout
  | @seq a b ha hb iha ihb =>
    intro source sourcePost result noInstall noInstallCode code run notError notTimeout
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at noInstall
    have preserved := WordSemStateFiniteExact.code_evaluate a source noInstall.1 noInstallCode
    have eq := WordSteps.steps_seq a b source
    rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at run
    rcases first : WordSemStateFiniteExact.evaluate a source with ⟨firstResult,middle⟩
    rw [first] at run eq preserved
    simp only at preserved
    cases firstResult with
    | none =>
      have firstBound := iha source middle none noInstall.1 noInstallCode code first (by simp) (by simp)
      have middleNoInstall : WordProps.noInstallCode middle.code := by simpa only [preserved] using noInstallCode
      have middleCode : ∀ loc arity q, sptLookup loc middle.code = some (arity,q) → LoopBlock q := by simpa only [preserved] using code
      have secondBound := ihb middle sourcePost result noInstall.2 middleNoInstall middleCode run notError notTimeout
      simp only at eq
      omega
    | some r =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      have firstBound := iha source middle (some r) noInstall.1 noInstallCode code first notError notTimeout
      simp only at eq
      omega


/-- A separately established source-step limit supplies a sufficient clock
for an actual compiled execution of the complete call sequence. -/
theorem callSequence_normalized {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (shape : CallSequence p) (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode source.code)
    (code : ∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q)
    (notTimeout : result ≠ some .timeOut) (stepBound : WordSteps.steps p source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate p source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false p (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL p < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens := by
  have used := callSequence_consumed ac shape source sourcePost result noInstall noInstallCode code
    premises.1 premises.2.1 notTimeout
  have normalized := normalize_of_consumed p source sourcePost result limit premises.1 notTimeout (used.trans stepBound)
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity q, sptLookup loc ({source with clock := limit}).code = some (arity,q) → LoopBlock q := code
  have normalizedNoInstall : WordProps.noInstallCode ({source with clock := limit}).code := noInstallCode
  have simulation := callSequence_zero ac shape {source with clock := limit} noInstall normalizedNoInstall normalizedCode
  exact simulation k f frame {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result bs bsPost n nPost compiled lens
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩

end SteppedFlapjack.WordToStackSteps
