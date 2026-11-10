import SteppedFlapjack.WordToStackSteps.CodeCostStable

/-! Target cost of sequences containing calls into loop-block code. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackSteps

/-- Compute a target bound from the source shape, actual compilation, code
map and a uniform clock limit. -/
def callSequenceCost {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (limit : Nat) (code : Spt (HolProg width)) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) : Nat :=
  if loopWord p then linearLoopCost limit (compNative ac false p bs kf).1 else
  match p with
  | .seq a b =>
      let first := compNative ac false a bs kf
      1 + callSequenceCost ac limit code a bs kf + callSequenceCost ac limit code b first.2 kf
  | .call none dest args none =>
      4 + loopOnlyCost 0 (callDestNative (width := width) dest args kf).1 + loopCodeCost limit code
  | .call (some _) _ _ _ => returningChainCost limit code (compNative ac false p bs kf).1
  | _ => 0
termination_by sizeOf p
decreasing_by all_goals simp_wf; try omega

/-- The sequence cost depends on code only through its maximum callee cost. -/
theorem callSequenceCost_eq_of_codeCost {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (limit : Nat) (a b : Spt (HolProg width))
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (same : loopCodeCost limit a = loopCodeCost limit b) :
    callSequenceCost ac limit a p bs kf = callSequenceCost ac limit b p bs kf := by
  conv_lhs => rw [callSequenceCost.eq_def]
  conv_rhs => rw [callSequenceCost.eq_def]
  split
  · rfl
  · cases hp : p <;> try rfl
    case seq x y =>
      simp only
      rw [callSequenceCost_eq_of_codeCost ac limit a b x bs kf same,
        callSequenceCost_eq_of_codeCost ac limit a b y (compNative ac false x bs kf).2 kf same]
    case call ret dest args handler =>
      cases ret with
      | none => cases handler <;> simp [same]
      | some r => exact returningChainCost_eq_of_codeCost limit a b _ same
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega


/-- Each atomic sequence component obeys the uniform structural cost. -/
theorem callSequence_atomic_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (k f frame : Nat) (lens : List Nat) (bs : AppList (BitVec width) × Nat)
    (related : stateRel ac k f frame source target lens 0) (clock : source.clock ≤ limit)
    (code : ∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q)
    (atomic : LoopBlock p ∨ (∃ dest args, p = .call none dest args none) ∨
      (∃ values names retCode l1 l2 dest args handler,
        p = .call (some (values,names,retCode,l1,l2)) dest args handler ∧ LoopBlock retCode ∧
        ∀ v hp h1 h2, handler = some (v,hp,h1,h2) → LoopBlock hp)) :
    steps ((compNative ac false p bs (k,f,frame)).1,target) ≤
      callSequenceCost ac limit target.code p bs (k,f,frame) := by
  rcases atomic with block | ⟨dest,args,rfl⟩ | ⟨values,names,retCode,l1,l2,dest,args,handler,rfl,retBlock,handlerBlock⟩
  · have shape := loopBlock_loop block
    rw [callSequenceCost.eq_def]
    simp only [shape, ↓reduceIte]
    apply linearLoopCostBound limit _ (loopWord_compiled ac p shape bs (k,f,frame)) target
    rw [← related.1]
    exact clock
  · have shape := relatedLoopCode ac k f frame source target lens related code
    have bound := compiledTail_bound ac dest args bs (k,f,frame) target shape
    have clocks : target.clock ≤ limit := by rw [← related.1]; exact clock
    have mono := loopCodeCost_mono target.code clocks
    rw [callSequenceCost.eq_def]
    simp [loopWord,straightWord]
    omega
  · have bound := compiledReturning_related_bound_at ac values names retCode l1 l2 dest args handler bs
      k f frame limit lens source target related clock code retBlock handlerBlock
    rw [callSequenceCost.eq_def]
    simp [loopWord,straightWord]
    exact bound


/-- Complete call-sequence target execution is bounded by the computed cost. -/
theorem callSequence_target_bound {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) {p : WordLangProgHOL (BitVec width)}
    (shape : CallSequence p) :
    ∀ (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
      (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (k f frame : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec width))
      (n nPost : Nat) (compiled : HolProg width),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode source.code →
      (∀ loc arity q, sptLookup loc source.code = some (arity,q) → LoopBlock q) →
      source.clock ≤ limit →
      (WordSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧
        result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
        postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
        compNative ac false p (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
        (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
        List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
        (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
        maxVarHOL p < 2 * frame + 2 * k) →
      steps (compiled,target) ≤ callSequenceCost ac limit target.code p (bs,n) (k,f,frame) := by
  induction shape with
  | block block =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := callSequence_atomic_bound ac limit _ source target k f frame lens (bs,n) facts.2.2.1 clock code (Or.inl block)
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | tail dest args =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := callSequence_atomic_bound ac limit _ source target k f frame lens (bs,n) facts.2.2.1 clock code (Or.inr (Or.inl ⟨dest,args,rfl⟩))
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | returning values names retCode l1 l2 dest args retBlock =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := callSequence_atomic_bound ac limit _ source target k f frame lens (bs,n) facts.2.2.1 clock code
      (Or.inr (Or.inr ⟨values,names,retCode,l1,l2,dest,args,none,rfl,retBlock,by simp⟩))
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | handler values names retCode l1 l2 dest args var handlerCode h1 h2 retBlock handlerBlock =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := callSequence_atomic_bound ac limit _ source target k f frame lens (bs,n) facts.2.2.1 clock code
      (Or.inr (Or.inr ⟨values,names,retCode,l1,l2,dest,args,some (var,handlerCode,h1,h2),rfl,retBlock,by intro v hp x y eq; cases eq; exact handlerBlock⟩))
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | @seq a b ha hb iha ihb =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    rcases facts with ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
    by_cases wholeBlock : loopWord (.seq a b) = true
    · have bound := linearLoopCostBound limit _ (loopWord_compiled ac (.seq a b) wholeBlock (bs,n) (k,f,frame)) target (by rw [← related.1]; exact clock)
      rw [compilation] at bound
      rw [callSequenceCost.eq_def]
      simp only [wholeBlock, ↓reduceIte, compilation]
      exact bound
    · simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noInstall
      rcases firstCompile : compNative ac false a (bs,n) (k,f,frame) with ⟨firstCode,firstBitmaps⟩
      rcases secondCompile : compNative ac false b firstBitmaps (k,f,frame) with ⟨secondCode,secondBitmaps⟩
      simp only [compNative,firstCompile,secondCompile] at compilation
      obtain ⟨compiledEq,bitmapEq⟩ := Prod.mk.inj compilation
      subst compiled
      have firstPrefix := compImpIsPrefix ac false b firstBitmaps (k,f,frame) secondCode secondBitmaps secondCompile
      rw [bitmapEq] at firstPrefix
      have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc → StackSem.locCheckExact target.code loc := by
        intro loc member
        apply labels loc
        rw [StackSem.getLabelsExact]
        exact Or.inl member
      have firstConventions : postAllocConventionsHOL k a = true := by
        simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL,Bool.and_eq_true] at conventions ⊢
        exact ⟨conventions.1.1,conventions.2.1.1,conventions.2.2.1⟩
      have firstFlat : flatExpConventions a = true := by simp only [flatExpConventions,Bool.and_eq_true] at flat; exact flat.1
      have firstMax : maxVarHOL a < 2*frame+2*k := by simp only [maxVarHOL] at maxBound; omega
      have secondConventions : postAllocConventionsHOL k b = true := by
        simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL,Bool.and_eq_true] at conventions ⊢
        exact ⟨conventions.1.2,conventions.2.1.2,conventions.2.2.2⟩
      have secondFlat : flatExpConventions b = true := by simp only [flatExpConventions,Bool.and_eq_true] at flat; exact flat.2
      have secondMax : maxVarHOL b < 2*frame+2*k := by simp only [maxVarHOL] at maxBound; omega
      rw [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.fix_clock_evaluate] at execution
      rcases firstRun : WordSemStateFiniteExact.evaluate a source with ⟨firstResult,middle⟩
      rw [firstRun] at execution
      have firstNotError : firstResult ≠ some .error := by
        cases firstResult with
        | none => simp
        | some value =>
          intro bad
          have eq : some value = result := (Prod.mk.inj execution).1
          exact notError (eq.symm.trans bad)
      have firstBound := iha source middle target firstResult k f frame lens bs firstBitmaps.1 n firstBitmaps.2 firstCode
        noInstall.1 noInstallCode code clock ⟨firstRun,firstNotError,related,firstConventions,firstFlat,firstCompile,
          lengthBound,bitmapBound,firstPrefix.trans bitmapPrefix,firstLabels,firstMax⟩
      have firstSim := callSequence_zero ac ha source noInstall.1 noInstallCode code
      obtain ⟨targetMiddle,targetResult,targetRun,firstConclusion⟩ := firstSim k f frame middle target firstResult
        bs firstBitmaps.1 n firstBitmaps.2 firstCode lens ⟨firstRun,firstNotError,related,firstConventions,firstFlat,firstCompile,
          lengthBound,bitmapBound,firstPrefix.trans bitmapPrefix,firstLabels,firstMax⟩
      have costEq : callSequenceCost ac limit target.code (.seq a b) (bs,n) (k,f,frame) =
          1 + callSequenceCost ac limit target.code a (bs,n) (k,f,frame) +
            callSequenceCost ac limit target.code b firstBitmaps (k,f,frame) := by
        rw [callSequenceCost.eq_def]
        simp [wholeBlock,firstCompile]
      rw [costEq,steps_seq,StackSemEvaluateClock.fixClockEvaluate,targetRun]
      cases targetResult with
      | some value => simp only; omega
      | none =>
        have firstNone : firstResult = none := by
          cases firstResult with
          | none => rfl
          | some value => simp [compCorrectResult] at firstConclusion
        subst firstResult
        have middleRelated : stateRel ac k f frame middle targetMiddle lens 0 := by simpa [compCorrectResult] using firstConclusion
        have mono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono firstCode target targetMiddle none targetRun
        have accounting := compImpLength ac false a (bs,n) (k,f,frame) firstCode firstBitmaps ⟨firstCompile,lengthBound⟩
        have secondBitmapBound : firstBitmaps.2-(appListAppend firstBitmaps.1).length ≤ targetMiddle.bitmaps.length := by
          rw [← accounting.2]; exact bitmapBound.trans mono.1.length_le
        have secondPrefix : (appListAppend secondBitmaps.1).IsPrefix (targetMiddle.bitmaps.drop (firstBitmaps.2-(appListAppend firstBitmaps.1).length)) := by
          rw [← accounting.2,bitmapEq]; exact bitmapPrefix.trans (mono.1.drop _)
        have secondLabels : ∀ loc, StackSem.getLabelsExact secondCode loc → StackSem.locCheckExact targetMiddle.code loc := by
          intro loc member
          apply LocationLabels.locCheckSubset target.code targetMiddle.code mono.2 loc
          apply labels loc
          rw [StackSem.getLabelsExact]
          exact Or.inr member
        have sourceSame := WordSemStateFiniteExact.code_evaluate a source noInstall.1 noInstallCode
        rw [firstRun] at sourceSame
        simp only at sourceSame
        have middleCode : ∀ loc arity q, sptLookup loc middle.code = some (arity,q) → LoopBlock q := by simpa only [sourceSame] using code
        have middleNoInstall : WordProps.noInstallCode middle.code := by simpa only [sourceSame] using noInstallCode
        have middleClock : middle.clock ≤ limit := by
          have h := WordSemStateFiniteExact.evaluate_clock a source none middle firstRun
          omega
        have secondBound := ihb middle sourcePost targetMiddle result k f frame lens firstBitmaps.1 secondBitmaps.1
          firstBitmaps.2 secondBitmaps.2 secondCode noInstall.2 middleNoInstall middleCode middleClock
          ⟨execution,notError,middleRelated,secondConventions,secondFlat,secondCompile,accounting.1,
            secondBitmapBound,secondPrefix,secondLabels,secondMax⟩
        have costStable := continuingCodeCost_stable ac k f frame limit lens a firstCode source middle target targetMiddle
          firstRun targetRun related firstConclusion noInstall.1 noInstallCode
        rw [callSequenceCost_eq_of_codeCost ac limit targetMiddle.code target.code b firstBitmaps (k,f,frame) costStable] at secondBound
        simp only
        omega


/-- A source-step limit yields an actual compiled execution with a computable target-step bound. -/
theorem callSequence_bounded {width : Nat} [NeZero width] {C F : Type}
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
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens ∧
      steps (compiled, {target with clock := limit}) ≤ callSequenceCost ac limit target.code p (bs,n) (k,f,frame) := by
  have used := callSequence_consumed ac shape source sourcePost result noInstall noInstallCode code
    premises.1 premises.2.1 notTimeout
  have normalized := normalize_of_consumed p source sourcePost result limit premises.1 notTimeout (used.trans stepBound)
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity q, sptLookup loc ({source with clock := limit}).code = some (arity,q) → LoopBlock q := code
  have normalizedNoInstall : WordProps.noInstallCode ({source with clock := limit}).code := noInstallCode
  have simulation := callSequence_zero ac shape {source with clock := limit} noInstall normalizedNoInstall normalizedCode
  obtain ⟨targetPost,targetResult,targetRun,conclusion⟩ := simulation k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result bs bsPost n nPost compiled lens
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have bound := callSequence_target_bound ac limit shape {source with clock := limit}
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit}
    result k f frame lens bs bsPost n nPost compiled noInstall normalizedNoInstall normalizedCode (by simp)
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  exact ⟨targetPost,targetResult,targetRun,conclusion,bound⟩


end SteppedFlapjack.WordToStackSteps
