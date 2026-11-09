import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import SteppedFlapjack.StackAllocSteps.LoopClockLinear
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.WordAllocSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
namespace SteppedFlapjack.WordToStackSteps

variable {width : Nat} [NeZero width]

/-- Maximum structural control weight of the actual finite Stack code table. -/
def stackCodeWeight (code : Spt (HolProg width)) : Nat :=
  maxListNat ((sptToAList code).map fun entry => stackControlWeight entry.2)

/-- Every looked-up code entry is bounded by the table maximum. -/
theorem stackCodeWeight_bound (code : Spt (HolProg width))
    (label : Nat) (p : HolProg width) (lookup : sptLookup label code = some p) :
    stackControlWeight p ≤ stackCodeWeight code := by
  have hlist : sptAListLookup label (sptToAList code) = some p := by
    have h := sptLookup_sptFromAList_sptToAList label code
    rw [lookup] at h
    simpa only [sptLookup_sptFromAList] using h
  have hmem := Flapjack.sptAListLookup_mem label (sptToAList code) p hlist
  apply le_maxListNat_of_mem
  exact List.mem_map.mpr ⟨(label,p),hmem,rfl⟩

/-- A direct Stack call uses only its named callee’s loop-free-call shape. -/
theorem directCall_linear_bound {C F : Type} (loc limit : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ limit)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps (.call none (.inl loc) none,s) ≤ 1 + stackCodeWeight s.code * (limit+1) := by
  rw [steps_call_none]
  cases found : sptLookup loc s.code with
  | none => simp [findCode,found]
  | some p =>
    by_cases zero : s.clock = 0
    · simp [findCode,found,zero]
    · have cost := stackControl_clock_bound p (shape p found) (decClock s)
      have maxBound := stackCodeWeight_bound s.code loc p found
      have factor : (decClock s).clock+1 ≤ limit+1 := by simp [decClock]; omega
      have scale := Nat.mul_le_mul maxBound factor
      simp only [findCode,found,zero,if_false]
      omega

/-- Freeing the caller frame preserves the linear direct-call bound. -/
theorem freeCall_linear_bound {C F : Type} (loc free limit : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ limit)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps (seqStackFreeNative free (.call none (.inl loc) none),s) ≤ 3 + stackCodeWeight s.code * (limit+1) := by
  unfold seqStackFreeNative
  split
  · have h := directCall_linear_bound loc limit s clockBound shape
    omega
  · rw [steps_seq]
    have hl : steps (.stackFree free,s) = 1 := steps_leaf _ s rfl
    rw [hl,StackSemEvaluateClock.fixClockEvaluate]
    rw [StackSemEvaluate.evaluate_stackFree]
    by_cases hu : (!s.useStack) = true
    · simp [hu]; omega
    · by_cases hs : s.stack.length < s.stackSpace + free
      · simp [hu,hs]; omega
      · simp only [hu,hs,if_false,Bool.false_eq_true]
        have h := directCall_linear_bound loc limit {s with stackSpace := s.stackSpace+free} clockBound shape
        simp only at h ⊢
        omega

/-- Native compilation of a direct tail call has a linear explicit bound. -/
theorem compiledDirect_linear_bound {C F : Type} (ac : AsmConfigExact width)
    (loc : Nat) (args : List Nat) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (s : StackSemStateFiniteExact width C F)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps ((compNative ac false (.call none (some loc) args none) bs kf).1,s) ≤
      5 + stackCodeWeight s.code * (s.clock+1) := by
  simp only [compNative,callDestNative]
  rw [steps_seq,StackSemEvaluateClock.fixClockEvaluate,StackSemEvaluate.evaluate_skip]
  have hp : steps (.skip,s) = 1 := steps_leaf _ s rfl
  rw [hp]
  have bound := freeCall_linear_bound loc (Compiler.Backend.WordToStack.stackFree (.inl loc : Sum Nat Nat) args.length kf.1 kf.2.1 kf.2.2)
    s.clock s (by rfl) shape
  simp only
  omega

/-- Extensional code equality gives the same computable maximum loop cost. -/
theorem stackCodeWeight_eq_of_lookup {width : Nat} [NeZero width]
    (a b : Spt (HolProg width))
    (same : ∀ key, sptLookup key a = sptLookup key b) :
    stackCodeWeight a = stackCodeWeight b := by
  have maxBound (xs : List Nat) (bound : Nat) (h : ∀ z, z ∈ xs → z ≤ bound) : maxListNat xs ≤ bound := by
    induction xs with
    | nil => simp [maxListNat]
    | cons z zs ih =>
      simp only [maxListNat, max_le_iff]
      exact ⟨h z (by simp), ih (by intro w hw; exact h w (by simp [hw]))⟩
  have bound (x y : Spt (HolProg width)) (h : ∀ key, sptLookup key x = sptLookup key y) :
      stackCodeWeight x ≤ stackCodeWeight y := by
    apply maxBound
    intro z hz
    obtain ⟨⟨key,value⟩, hm, rfl⟩ := List.mem_map.mp hz
    have lookup := sptToAList_entry_lookup x key value hm
    exact stackCodeWeight_bound y key value ((h key).symm.trans lookup)

  exact Nat.le_antisymm (bound a b same) (bound b a (fun key => (same key).symm))


/-- A continuing related execution preserves the source code map's target
cost: the source no-install theorem fixes the domain, while StackSem code
monotonicity fixes the entries in that domain. -/
theorem continuingStackWeight_stable {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (lens : List Nat)
    (p : WordLangProgHOL (BitVec width)) (compiled : HolProg width)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target targetPost : StackSemStateFiniteExact width C F)
    (sourceRun : WordSemStateFiniteExact.evaluate p source = (none,sourcePost))
    (targetRun : StackSemEvaluate.evaluate (compiled,target) = (none,targetPost))
    (related : stateRel ac k f frame source target lens 0)
    (conclusion : compCorrectResult ac k f frame source sourcePost targetPost none none lens)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode source.code) :
    stackCodeWeight targetPost.code = stackCodeWeight target.code := by
  have sourceSame := WordSemStateFiniteExact.code_evaluate p source noInstall noInstallCode
  rw [sourceRun] at sourceSame
  have postRelated : stateRel ac k f frame sourcePost targetPost lens 0 := by
    simpa [compCorrectResult] using conclusion
  have domain := relatedTargetCodeDomains ac k f frame lens source sourcePost target targetPost related postRelated sourceSame
  have growth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono compiled target targetPost none targetRun).2
  exact stackCodeWeight_eq_of_lookup targetPost.code target.code
    (lookup_eq_of_growth_and_domain target.code targetPost.code growth domain)



/-- Computable direct-tail Stack cost, linear in the supplied clock limit. -/
def directTailLinearCost (ac : AsmConfigExact width) (limit : Nat) (code : Spt (HolProg width))
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : Nat :=
  if loopWord p then stackControlWeight (compNative ac false p bs kf).1 * (limit+1) else
  match p with
  | .seq a b =>
      let first := compNative ac false a bs kf
      1 + directTailLinearCost ac limit code a bs kf + directTailLinearCost ac limit code b first.2 kf
  | .call none (some _) _ none => 5 + stackCodeWeight code * (limit+1)
  | _ => 0
termination_by sizeOf p
decreasing_by all_goals simp_wf; try omega

/-- Only the code table maximum matters to the computed cost. -/
theorem directTailLinearCost_eq_of_codeWeight (ac : AsmConfigExact width) (limit : Nat)
    (a b : Spt (HolProg width)) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (same : stackCodeWeight a = stackCodeWeight b) :
    directTailLinearCost ac limit a p bs kf = directTailLinearCost ac limit b p bs kf := by
  conv_lhs => rw [directTailLinearCost.eq_def]
  conv_rhs => rw [directTailLinearCost.eq_def]
  split
  · rfl
  · cases hp : p <;> try rfl
    case seq x y =>
      simp only
      rw [directTailLinearCost_eq_of_codeWeight ac limit a b x bs kf same,
        directTailLinearCost_eq_of_codeWeight ac limit a b y (compNative ac false x bs kf).2 kf same]
    case call ret dest args handler =>
      cases ret <;> cases dest <;> cases handler <;> simp [same]
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

/-- A direct tail call obeys the computed linear cost. -/
theorem directTail_atomic_linear_bound {C F : Type} (ac : AsmConfigExact width) (limit loc reg : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (k f frame : Nat) (lens : List Nat) (bs : AppList (BitVec width) × Nat)
    (related : stateRel ac k f frame source target lens 0) (clock : source.clock ≤ limit)
    (code : RegTailLocalCode (.call none (some loc) [reg] none) source.code) :
    steps ((compNative ac false (.call none (some loc) [reg] none) bs (k,f,frame)).1,target) ≤
      directTailLinearCost ac limit target.code (.call none (some loc) [reg] none) bs (k,f,frame) := by
  have targetShape := relatedLoopCode_at ac k f frame loc source target lens related (code loc (.call loc reg))
  have bound := compiledDirect_linear_bound ac loc [reg] bs (k,f,frame) target targetShape
  have clocks : target.clock ≤ limit := by rw [← related.1]; exact clock
  have mono := Nat.mul_le_mul_left (stackCodeWeight target.code) (show target.clock+1 ≤ limit+1 by omega)
  rw [directTailLinearCost.eq_def]
  simp [loopWord,straightWord]
  omega

/-- A supported entry executes within its computed linear Stack cost. -/
theorem regTail_target_linear_bound {C F : Type} (ac : AsmConfigExact width) (limit : Nat)
    {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    ∀ (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
      (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (k f frame : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec width))
      (n nPost : Nat) (compiled : HolProg width),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode source.code →
      RegTailLocalCode p source.code → source.clock ≤ limit →
      (WordSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧
        result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
        postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
        compNative ac false p (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
        (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
        List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
        (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
        maxVarHOL p < 2 * frame + 2 * k) →
      steps (compiled,target) ≤ directTailLinearCost ac limit target.code p (bs,n) (k,f,frame) := by
  induction shape with
  | branch branch =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have block := flat_branch_block branch facts.2.2.2.2.1
    have shape := loopBlock_loop block
    have bound := stackControl_clock_bound _ (loopWord_compiled ac _ shape (bs,n) (k,f,frame)) target
    have targetClock : target.clock ≤ limit := by rw [← facts.2.2.1.1]; exact clock
    have bound := bound.trans (Nat.mul_le_mul_left _ (show target.clock+1 ≤ limit+1 by omega))
    rw [facts.2.2.2.2.2.1] at bound
    rw [directTailLinearCost.eq_def]
    simp only [shape,↓reduceIte,facts.2.2.2.2.2.1]
    exact bound
  | call loc reg =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := directTail_atomic_linear_bound ac limit loc reg source target k f frame lens (bs,n) facts.2.2.1 clock code
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | @seq a b ha hb iha ihb =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have codeA : RegTailLocalCode a source.code := fun loc h => code loc (.left h)
    have codeB : RegTailLocalCode b source.code := fun loc h => code loc (.right h)
    rcases facts with ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
    by_cases wholeBlock : loopWord (.seq a b) = true
    · have bound := stackControl_clock_bound _ (loopWord_compiled ac (.seq a b) wholeBlock (bs,n) (k,f,frame)) target
      have targetClock : target.clock ≤ limit := by rw [← related.1]; exact clock
      have bound := bound.trans (Nat.mul_le_mul_left _ (show target.clock+1 ≤ limit+1 by omega))
      rw [compilation] at bound
      rw [directTailLinearCost.eq_def]
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
        noInstall.1 noInstallCode codeA clock ⟨firstRun,firstNotError,related,firstConventions,firstFlat,firstCompile,
          lengthBound,bitmapBound,firstPrefix.trans bitmapPrefix,firstLabels,firstMax⟩
      have firstSim := regTail_zero_local ac ha source firstFlat noInstallCode codeA
      obtain ⟨targetMiddle,targetResult,targetRun,firstConclusion⟩ := firstSim k f frame middle target firstResult
        bs firstBitmaps.1 n firstBitmaps.2 firstCode lens ⟨firstRun,firstNotError,related,firstConventions,firstFlat,firstCompile,
          lengthBound,bitmapBound,firstPrefix.trans bitmapPrefix,firstLabels,firstMax⟩
      have costEq : directTailLinearCost ac limit target.code (.seq a b) (bs,n) (k,f,frame) =
          1 + directTailLinearCost ac limit target.code a (bs,n) (k,f,frame) +
            directTailLinearCost ac limit target.code b firstBitmaps (k,f,frame) := by
        rw [directTailLinearCost.eq_def]
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
        have middleCode : RegTailLocalCode b middle.code := by simpa only [sourceSame] using codeB
        have middleNoInstall : WordProps.noInstallCode middle.code := by simpa only [sourceSame] using noInstallCode
        have middleClock : middle.clock ≤ limit := by
          have h := WordSemStateFiniteExact.evaluate_clock a source none middle firstRun
          omega
        have secondBound := ihb middle sourcePost targetMiddle result k f frame lens firstBitmaps.1 secondBitmaps.1
          firstBitmaps.2 secondBitmaps.2 secondCode noInstall.2 middleNoInstall middleCode middleClock
          ⟨execution,notError,middleRelated,secondConventions,secondFlat,secondCompile,accounting.1,
            secondBitmapBound,secondPrefix,secondLabels,secondMax⟩
        have costStable := continuingStackWeight_stable ac k f frame lens a firstCode source middle target targetMiddle
          firstRun targetRun related firstConclusion noInstall.1 noInstallCode
        rw [directTailLinearCost_eq_of_codeWeight ac limit targetMiddle.code target.code b firstBitmaps (k,f,frame) costStable] at secondBound
        simp only
        omega


/-- Normalize a source visit limit and simulate with an explicit linear Stack cost. -/
theorem regTail_bounded_linear {width : Nat} [NeZero width] {C F : Type}
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
      maxVarHOL p < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens ∧
      steps (compiled, {target with clock := limit}) ≤ directTailLinearCost ac limit target.code p (bs,n) (k,f,frame) := by
  have used := regTail_consumed_local ac shape source sourcePost result premises.2.2.2.2.1 noInstallCode code
    premises.1 premises.2.1 notTimeout
  have normalized := normalize_of_consumed p source sourcePost result limit premises.1 notTimeout (used.trans stepBound)
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : RegTailLocalCode p ({source with clock := limit}).code := code
  have normalizedNoInstall : WordProps.noInstallCode ({source with clock := limit}).code := noInstallCode
  have simulation := regTail_zero_local ac shape {source with clock := limit} premises.2.2.2.2.1 normalizedNoInstall normalizedCode
  obtain ⟨targetPost,targetResult,targetRun,conclusion⟩ := simulation k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result bs bsPost n nPost compiled lens
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have bound := regTail_target_linear_bound ac limit shape {source with clock := limit}
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit}
    result k f frame lens bs bsPost n nPost compiled noInstall normalizedNoInstall normalizedCode (by simp)
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  exact ⟨targetPost,targetResult,targetRun,conclusion,bound⟩

/-- The computed cost is bounded by a code-derived coefficient times the clock. -/
theorem directTailLinearCost_le (ac : AsmConfigExact width) (limit : Nat) (code : Spt (HolProg width))
    (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat) :
    directTailLinearCost ac limit code p bs kf ≤ directTailLinearCost ac 0 code p bs kf * (limit+1) := by
  conv_lhs => rw [directTailLinearCost.eq_def]
  conv_rhs => rw [directTailLinearCost.eq_def]
  split
  · simp
  · cases hp : p <;> try simp
    case seq a b =>
      have ha := directTailLinearCost_le ac limit code a bs kf
      have hb := directTailLinearCost_le ac limit code b (Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false a bs kf).2 kf
      nlinarith
    case call ret dest args handler =>
      cases ret <;> cases dest <;> cases handler <;> simp
      all_goals nlinarith
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf; try omega

end SteppedFlapjack.WordToStackSteps
