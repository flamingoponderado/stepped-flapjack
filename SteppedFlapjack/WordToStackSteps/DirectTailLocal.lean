import SteppedFlapjack.WordToStackSteps.CallSequenceCost
import SteppedFlapjack.WordAllocSteps.TailEntry

/-! Local callee conditions for direct tail calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open SteppedFlapjack.WordAllocSteps
open Flapjack.Compiler.Backend.WordToStack.Native SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

/-- A direct Word lookup can only reach the named code-table entry. -/
theorem directWordFind_block (loc : Nat) (xs values : List (WordLocW width))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (ssizes : Spt Nat)
    (callee : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (localShape : ∀ arity q, sptLookup loc code = some (arity,q) → LoopBlock q)
    (found : wordSemFindCode (some loc) xs code ssizes = some (values,callee,ss)) : LoopBlock callee := by
  cases h : sptLookup loc code with
  | none => simp [wordSemFindCode,h] at found
  | some entry =>
    obtain ⟨arity,prog⟩ := entry
    simp only [wordSemFindCode,h] at found
    split at found
    · simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨_,rfl,_⟩ := found
      exact localShape arity prog h
    · contradiction

/-- The direct tail-call simulation needs only the named callee's shape. -/
theorem directTail_zero_local {C F : Type} (ac : AsmConfigExact width) (loc : Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (code : ∀ arity prog, sptLookup loc source.code = some (arity,prog) → LoopBlock prog) :
    ZeroSimulation ac (.call none (some loc) args none) source := by
  apply zeroCallTail ac (some loc) args none source
  intro xs args1 prog ss guard
  exact loopBlock_zero ac prog _ (directWordFind_block loc xs args1 source.code source.stackSize prog ss code guard.2.2.1)

/-- Only the named source function needs to be a loop block to establish
that its compiled Stack code is loop-only. -/
theorem relatedLoopCode_at {C F : Type} (ac : AsmConfigExact width) (k f frame loc : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (lens : List Nat) (related : stateRel ac k f frame source target lens 0)
    (lookupSource : ∃ arity prog, sptLookup loc source.code = some (arity,prog) ∧ LoopBlock prog) :
    ∀ p, sptLookup loc target.code = some p → loopOnly p = true := by
  intro p lookup
  obtain ⟨arity,prog,sourceLookup,block⟩ := lookupSource
  have rel := related
  unfold stateRel at rel
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,functions,_,_,_⟩ := rel
  obtain ⟨_,_,bs,j,bs2,j2,frame2,targetProg,compiled,_,_,_,targetLookup,_⟩ := functions loc prog arity sourceLookup
  have eq : p = targetProg := by rw [lookup] at targetLookup; exact Option.some.inj targetLookup
  subst p
  have shape := loopOnly_compileProg ac prog block arity k (bs,j)
  rw [compiled] at shape
  exact shape

/-- A direct Stack tail call needs a loop-only bound solely at its destination. -/
theorem directTargetTail_bound_at {C F : Type} (loc limit : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ limit)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps (.call none (.inl loc) none, s) ≤ 1 + loopCodeCost limit s.code := by
  rw [steps_call_none]
  cases found : sptLookup loc s.code with
  | none => simp [findCode,found]
  | some p =>
    by_cases zero : s.clock = 0
    · simp [findCode,found,zero]
    · have cost := loopOnlyCostBound limit p (shape p found) (decClock s) (by simp [decClock]; omega)
      have maxBound := loopCodeCost_bound limit s.code loc p found
      simp only [findCode,found,zero,if_false]
      omega

/-- Freeing the caller frame retains the local direct-callee condition. -/
theorem directFreeTail_bound {C F : Type} (loc free limit : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ limit)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps (seqStackFreeNative free (.call none (.inl loc) none),s) ≤ 3 + loopCodeCost limit s.code := by
  unfold seqStackFreeNative
  split
  · have h := directTargetTail_bound_at loc limit s clockBound shape
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
        have h := directTargetTail_bound_at loc limit {s with stackSpace := s.stackSpace+free} clockBound shape
        simp only at h ⊢
        omega

/-- Compiled direct tail-call visits depend only on its named target's shape. -/
theorem compiledDirectTail_local_bound {C F : Type} (ac : AsmConfigExact width)
    (loc : Nat) (args : List Nat) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (s : StackSemStateFiniteExact width C F)
    (shape : ∀ p, sptLookup loc s.code = some p → loopOnly p = true) :
    steps ((compNative ac false (.call none (some loc) args none) bs kf).1,s) ≤
      4 + loopOnlyCost 0 (callDestNative (width := width) (some loc) args kf).1 + loopCodeCost s.clock s.code := by
  simp only [compNative,callDestNative]
  rw [steps_seq,StackSemEvaluateClock.fixClockEvaluate,StackSemEvaluate.evaluate_skip]
  have hp : steps (.skip,s) = 1 := steps_leaf _ s rfl
  rw [hp]
  have bound := directFreeTail_bound loc (Compiler.Backend.WordToStack.stackFree (.inl loc : Sum Nat Nat) args.length kf.1 kf.2.1 kf.2.2)
    s.clock s (by rfl) shape
  simp only [loopOnlyCost]
  omega


/-- A completed direct call consumes at most its Word visits, using only
the named callee shape. -/
theorem directTail_consumed_local {C F : Type} (loc : Nat) (args : List Nat)
    (s post : WordSemStateFiniteExact width (Nat × C) F) (res : Option (WordSemResult width))
    (code : ∀ arity prog, sptLookup loc s.code = some (arity, prog) → LoopBlock prog)
    (run : WordSemStateFiniteExact.evaluate (.call none (some loc) args none) s = (res, post))
    (notError : res ≠ some .error) (notTimeout : res ≠ some .timeOut) :
    s.clock - post.clock ≤ WordSteps.steps (.call none (some loc) args none) s := by
  rw [WordSemStateFiniteExact.evaluate] at run
  cases hargs : WordSemStateFiniteExact.getVars args s with
  | none => simp [hargs] at run; exact False.elim (notError run.1.symm)
  | some xs =>
    simp only [hargs] at run
    cases hbad : wordSemBadDestArgs (some loc) args with
    | true => simp [hbad] at run; exact False.elim (notError run.1.symm)
    | false =>
      simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at run
      cases hfind : wordSemFindCode (some loc) xs s.code s.stackSize with
      | none => simp [hfind] at run; exact False.elim (notError run.1.symm)
      | some found =>
        rcases found with ⟨values, callee, ss⟩
        simp only [hfind] at run
        by_cases hz : s.clock = 0
        · simp [hz] at run
          exact False.elim (notTimeout run.1.symm)
        · simp only [hz, ↓reduceDIte] at run
          rcases he : WordSemStateFiniteExact.evaluate callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s)) with ⟨r, t⟩
          rw [he] at run
          by_cases hb : wordSemBadFunReturn r = true
          · simp [hb] at run
            exact False.elim (notError run.1.symm)
          · simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            have hc := WordSteps.loopWord_consumption callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s))
              (loopBlock_loop (directWordFind_block loc xs values s.code s.stackSize callee ss code hfind))
            rw [he] at hc
            rw [WordSteps.steps_call_tail (some loc) args s xs values ss callee hargs hbad hfind hz]
            change s.clock - 1 ≤ t.clock + WordSteps.steps callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s)) at hc
            omega

/-- Callee shape is required only for direct calls syntactically present in
the entry, not for unrelated functions in the code table. -/
def RegTailLocalCode (p : WordLangProgHOL (BitVec width))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ loc, RegTailCalls p loc → ∃ arity q, sptLookup loc code = some (arity,q) ∧ LoopBlock q

/-- A flat direct-tail entry has a zero-extra-clock simulation using only its
own direct call destinations. -/
theorem regTail_zero_local {C F : Type} (ac : AsmConfigExact width)
    {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    ∀ (source : WordSemStateFiniteExact width (Nat × C) F),
      flatExpConventions p = true → WordProps.noInstallCode source.code → RegTailLocalCode p source.code →
      ZeroSimulation ac p source := by
  induction shape with
  | branch h => intro source flat _ _; exact loopBlock_zero ac _ source (flat_branch_block h flat)
  | call loc reg =>
    intro source flat noInstallCode code
    obtain ⟨arity,q,lookup,block⟩ := code loc (.call loc reg)
    apply directTail_zero_local ac loc [reg] source
    intro arity' q' h
    have eq := Option.some.inj (lookup.symm.trans h)
    cases eq
    exact block
  | @seq a b ha hb iha ihb =>
    intro source flat noInstallCode code
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    have ca : RegTailLocalCode a source.code := fun loc h => code loc (.left h)
    have cb : RegTailLocalCode b source.code := fun loc h => code loc (.right h)
    apply zeroSeq ac a b source (iha source flat.1 noInstallCode ca)
    intro result middle run
    have eq : middle.code = source.code := by
      have preserved := WordSemStateFiniteExact.code_evaluate a source (regTail_noInstall ha) noInstallCode
      rw [← run.1] at preserved
      exact preserved
    exact ihb middle flat.2 (by simpa only [eq] using noInstallCode) (by simpa only [eq] using cb)

/-- Completed flat direct-tail entries consume at most their Word visits. -/
theorem regTail_consumed_local {C F : Type} (_ac : AsmConfigExact width)
    {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    ∀ (source post : WordSemStateFiniteExact width (Nat × C) F) (result : Option (WordSemResult width)),
      flatExpConventions p = true → WordProps.noInstallCode source.code → RegTailLocalCode p source.code →
      WordSemStateFiniteExact.evaluate p source = (result,post) → result ≠ some .error → result ≠ some .timeOut →
      source.clock-post.clock ≤ WordSteps.steps p source := by
  induction shape with
  | branch h =>
    intro source post result flat _ _ run _ _
    have block := flat_branch_block h flat
    have bound := WordSteps.loopWord_consumption _ source (loopBlock_loop block)
    rw [run] at bound
    simp only at bound
    omega
  | call loc reg =>
    intro source post result flat noInstallCode code run notError notTimeout
    obtain ⟨arity,q,lookup,block⟩ := code loc (.call loc reg)
    refine directTail_consumed_local loc [reg] source post result ?_ run notError notTimeout
    intro arity' q' h
    have eq := Option.some.inj (lookup.symm.trans h)
    cases eq
    exact block
  | @seq a b ha hb iha ihb =>
    intro source post result flat noInstallCode code run notError notTimeout
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    have ca : RegTailLocalCode a source.code := fun loc h => code loc (.left h)
    have cb : RegTailLocalCode b source.code := fun loc h => code loc (.right h)
    have preserved := WordSemStateFiniteExact.code_evaluate a source (regTail_noInstall ha) noInstallCode
    have eq := WordSteps.steps_seq a b source
    rw [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.fix_clock_evaluate] at run
    rcases first : WordSemStateFiniteExact.evaluate a source with ⟨out,middle⟩
    rw [first] at run eq preserved
    simp only at preserved
    cases out with
    | none =>
      have firstBound := iha source middle none flat.1 noInstallCode ca first (by simp) (by simp)
      have secondBound := ihb middle post result flat.2 (by simpa only [preserved] using noInstallCode)
        (by simpa only [preserved] using cb) run notError notTimeout
      simp only at eq
      omega
    | some r =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      have firstBound := iha source middle (some r) flat.1 noInstallCode ca first notError notTimeout
      simp only at eq
      omega

/-- A direct entry component's target cost needs only its destination's
source code entry to be a supported loop block. -/
theorem directTail_atomic_bound {C F : Type} (ac : AsmConfigExact width) (limit loc reg : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (k f frame : Nat) (lens : List Nat) (bs : AppList (BitVec width) × Nat)
    (related : stateRel ac k f frame source target lens 0) (clock : source.clock ≤ limit)
    (code : RegTailLocalCode (.call none (some loc) [reg] none) source.code) :
    steps ((compNative ac false (.call none (some loc) [reg] none) bs (k,f,frame)).1,target) ≤
      callSequenceCost ac limit target.code (.call none (some loc) [reg] none) bs (k,f,frame) := by
  have targetShape := relatedLoopCode_at ac k f frame loc source target lens related (code loc (.call loc reg))
  have bound := compiledDirectTail_local_bound ac loc [reg] bs (k,f,frame) target targetShape
  have clocks : target.clock ≤ limit := by rw [← related.1]; exact clock
  have mono := loopCodeCost_mono target.code clocks
  rw [callSequenceCost.eq_def]
  simp [loopWord,straightWord]
  omega

/-- Target execution of a flat direct-tail entry is bounded using only its
syntactic direct callees, including across continuing prefixes. -/
theorem regTail_target_bound_local {C F : Type} (ac : AsmConfigExact width) (limit : Nat)
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
      steps (compiled,target) ≤ callSequenceCost ac limit target.code p (bs,n) (k,f,frame) := by
  induction shape with
  | branch branch =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have block := flat_branch_block branch facts.2.2.2.2.1
    have shape := loopBlock_loop block
    have bound := loopOnlyCostBound limit _ (loopWord_compiled ac _ shape (bs,n) (k,f,frame)) target (by rw [← facts.2.2.1.1]; exact clock)
    rw [facts.2.2.2.2.2.1] at bound
    rw [callSequenceCost.eq_def]
    simp only [shape,↓reduceIte,facts.2.2.2.2.2.1]
    exact bound
  | call loc reg =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have bound := directTail_atomic_bound ac limit loc reg source target k f frame lens (bs,n) facts.2.2.1 clock code
    rw [facts.2.2.2.2.2.1] at bound
    exact bound
  | @seq a b ha hb iha ihb =>
    intro source sourcePost target result k f frame lens bs bsPost n nPost compiled noInstall noInstallCode code clock facts
    have codeA : RegTailLocalCode a source.code := fun loc h => code loc (.left h)
    have codeB : RegTailLocalCode b source.code := fun loc h => code loc (.right h)
    rcases facts with ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
    by_cases wholeBlock : loopWord (.seq a b) = true
    · have bound := loopOnlyCostBound limit _ (loopWord_compiled ac (.seq a b) wholeBlock (bs,n) (k,f,frame)) target (by rw [← related.1]; exact clock)
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
        noInstall.1 noInstallCode codeA clock ⟨firstRun,firstNotError,related,firstConventions,firstFlat,firstCompile,
          lengthBound,bitmapBound,firstPrefix.trans bitmapPrefix,firstLabels,firstMax⟩
      have firstSim := regTail_zero_local ac ha source firstFlat noInstallCode codeA
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
        have middleCode : RegTailLocalCode b middle.code := by simpa only [sourceSame] using codeB
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

/-- A source-visit limit gives the actual compiled Stack execution and
a computed target cost without a whole-code-table shape condition. -/
theorem regTail_bounded_local {width : Nat} [NeZero width] {C F : Type}
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
      steps (compiled, {target with clock := limit}) ≤ callSequenceCost ac limit target.code p (bs,n) (k,f,frame) := by
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
  have bound := regTail_target_bound_local ac limit shape {source with clock := limit}
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit}
    result k f frame lens bs bsPost n nPost compiled noInstall normalizedNoInstall normalizedCode (by simp)
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  exact ⟨targetPost,targetResult,targetRun,conclusion,bound⟩
end SteppedFlapjack.WordToStackSteps
