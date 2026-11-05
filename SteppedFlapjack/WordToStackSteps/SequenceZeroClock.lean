import SteppedFlapjack.WordToStackSteps.InstructionZeroClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq

/-! Zero-extra-clock simulation composition for Word-to-Stack sequences. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

def ZeroSimulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, target) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens


theorem zeroSeqFirstNonNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        ZeroSimulation ac second middle) ∧ ZeroSimulation ac first source)
    (firstNonNone : (WordSemStateFiniteExact.evaluate first source).1 ≠ none) :
    ZeroSimulation ac (.seq first second) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNonNone execution
  cases firstResult with
  | none => exact False.elim (firstNonNone rfl)
  | some value =>
    obtain ⟨resultEq, sourceEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    obtain ⟨targetPost, targetResult, targetRun, conclusion⟩ :=
      ih.2 k f frame middle target (some value) bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, notError, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩
    have targetNonNone : targetResult ≠ none := by
      intro eq
      subst targetResult
      simp [compCorrectResult] at conclusion
    refine ⟨targetPost, targetResult, ?_, conclusion⟩
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
    cases targetResult with
    | none => exact False.elim (targetNonNone rfl)
    | some output => rfl


theorem zeroSeqFirstNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        ZeroSimulation ac second middle) ∧ ZeroSimulation ac first source)
    (firstNone : (WordSemStateFiniteExact.evaluate first source).1 = none) :
    ZeroSimulation ac (.seq first second) source := by
  classical
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  have secondConventions : postAllocConventionsHOL k second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.2, conventions.2.1.2, conventions.2.2.2⟩
  have secondFlat : flatExpConventions second = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.2
  have secondMax : maxVarHOL second < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNone execution
  cases firstResult with
  | some value => cases firstNone
  | none =>
    obtain ⟨targetMiddle, firstTargetResult, targetRun, firstConclusion⟩ :=
      ih.2 k f frame middle target none bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, by simp, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩
    cases firstTargetResult with
    | some value =>
      simp [compCorrectResult] at firstConclusion
      rcases firstConclusion with ⟨valueEq, events, resource⟩
      subst value
      have finalEvents := WordSemStateFiniteExact.evaluate_io_events_mono
        second middle result sourcePost execution
      have resourceThe : miscThe (middle.stackLimit + 1) middle.stackMax > middle.stackLimit := by
        cases h : middle.stackMax <;> simp_all [miscThe]
      have finalResourceThe := WordSemStateFiniteExact.evaluate_stack_limit_stack_max
        second middle result sourcePost ⟨execution, resourceThe⟩
      have finalResource : sourcePost.stackMax.getD (sourcePost.stackLimit + 1) >
          sourcePost.stackLimit := by
        cases h : sourcePost.stackMax <;> simp_all [miscThe]
      have dimension : goodDimindex width := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have mismatch : result.map compileResult ≠ some (.halt (.word 2)) := by
        cases result with
        | none => simp
        | some value =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact Ne.symm ((haltEqCompileResult value).2 dimension)
      refine ⟨targetMiddle, some (.halt (.word 2)), ?_, ?_⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
        rfl
      · unfold compCorrectResult
        split
        · exact ⟨rfl, events.trans finalEvents, finalResource⟩
        · rename_i equal
          exact False.elim (mismatch (by simpa using equal))
    | none =>
      simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false,
        ↓reduceIte] at firstConclusion
      have accounting := compImpLength ac false first (bs, n) (k, f, frame)
        firstCode middleBitmaps ⟨firstCompile, lengthBound⟩
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        firstCode target targetMiddle none targetRun
      have gap := accounting.2
      have secondBitmapBound : middleBitmaps.2 - (appListAppend middleBitmaps.1).length ≤
          targetMiddle.bitmaps.length := by
        rw [← gap]
        exact bitmapBound.trans mono.1.length_le
      have secondPrefix : (appListAppend finalBitmaps.1).IsPrefix
          (targetMiddle.bitmaps.drop
            (middleBitmaps.2 - (appListAppend middleBitmaps.1).length)) := by
        rw [← gap, bitmapEq]
        exact bitmapPrefix.trans (mono.1.drop _)
      have secondLabels : ∀ loc, StackSem.getLabelsExact secondCode loc →
          StackSem.locCheckExact targetMiddle.code loc := by
        intro loc member
        apply LocationLabels.locCheckSubset target.code targetMiddle.code mono.2 loc
        apply labels loc
        rw [StackSem.getLabelsExact]
        exact Or.inr member
      obtain ⟨targetPost, targetResult, secondRun, conclusion⟩ :=
        ih.1 none middle ⟨firstRun.symm, rfl⟩ k f frame sourcePost targetMiddle
          result middleBitmaps.1 finalBitmaps.1 middleBitmaps.2 finalBitmaps.2
          secondCode lens ⟨execution, notError, firstConclusion, secondConventions,
            secondFlat, secondCompile, accounting.1, secondBitmapBound, secondPrefix,
            secondLabels, secondMax⟩
      have handlerEq : middle.handler = source.handler := by
        have preserved := WordSemStackEq.evaluateStackSwap first source
        unfold WordSemStackEq.stackSwapPost at preserved
        rw [firstRun] at preserved
        exact preserved.2.1
      have finalConclusion : compCorrectResult ac k f frame source sourcePost
          targetPost result targetResult lens := by
        unfold compCorrectResult at conclusion ⊢
        rw [handlerEq] at conclusion
        exact conclusion
      refine ⟨targetPost, targetResult, ?_, finalConclusion⟩
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
      exact secondRun


/-- Zero-clock simulations compose across both sequence outcomes. -/
theorem zeroSeq {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (a b : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (first : ZeroSimulation ac a source)
    (second : ∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate a source ∧ result = none →
        ZeroSimulation ac b middle) : ZeroSimulation ac (.seq a b) source := by
  by_cases h : (WordSemStateFiniteExact.evaluate a source).1 = none
  · exact zeroSeqFirstNone ac a b source ⟨second, first⟩ h
  · exact zeroSeqFirstNonNone ac a b source ⟨second, first⟩ h

/-- Source programs consisting of machine instructions and sequences. -/
inductive InstructionBlock {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | inst (i) : InstructionBlock (.inst i)
  | seq {a b} : InstructionBlock a → InstructionBlock b → InstructionBlock (.seq a b)

/-- Every instruction block has a zero-extra-clock semantic simulation. -/
theorem instructionBlock_zero {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (block : InstructionBlock p) :
    ∀ source : WordSemStateFiniteExact width (Nat × C) F, ZeroSimulation ac p source := by
  induction block with
  | inst i =>
    intro source k f frame sourcePost target result bs bsPost n nPost compiled lens premises
    obtain ⟨post, out, run, related, _⟩ :=
      inst_zeroClock ac i source sourcePost target result k f frame bs bsPost n nPost compiled lens premises
    exact ⟨post, out, run, related⟩
  | seq ha hb iha ihb =>
    intro source
    exact zeroSeq ac _ _ source (iha source) (fun _ middle _ => ihb middle)


/-- Instruction blocks belong to the checked straight-line fragment. -/
theorem instructionBlock_straight {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (block : InstructionBlock p) : straightWord p = true := by
  induction block with
  | inst i => rfl
  | seq ha hb iha ihb => simp [straightWord, iha, ihb]

theorem instructionBlock_loop {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (block : InstructionBlock p) : loopWord p = true := by
  induction block with
  | inst i => rfl
  | seq ha hb iha ihb => simp [loopWord, iha, ihb]

/-- An instruction block replays on source-step-bounded clocks and its actual
compiled execution preserves the original correctness relation within a
computable target-step bound. -/
theorem instructionBlock_normalized {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width)) (block : InstructionBlock p)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (notTimeout : result ≠ some .timeOut) (stepsBound : WordSteps.steps p source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate p source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
      compNative ac false p (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL p < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
        targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := limit}) ≤ StackAllocSteps.loopOnlyCost 0 compiled := by
  have straight := instructionBlock_straight block
  have frag := instructionBlock_loop block
  have normalized := loopWord_normalized_run p source sourcePost result limit frag
    premises.1 notTimeout stepsBound
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have simulation := instructionBlock_zero (C := C) (F := F) ac p block {source with clock := limit}
  obtain ⟨post, out, run, conclusion⟩ := simulation k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result bs bsPost n nPost compiled lens
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have shape := straightWord_compiled ac p straight (bs, n) (k, f, frame)
  rw [premises.2.2.2.2.2.1] at shape
  exact ⟨post, out, run, conclusion, StackRemoveSteps.straightLineSteps compiled shape _⟩

end SteppedFlapjack.WordToStackSteps
