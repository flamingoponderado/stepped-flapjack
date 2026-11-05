import SteppedFlapjack.WordToStackSteps.IfZeroClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Loop

/-! Zero-extra-clock loop simulation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Loop
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

def ZeroLoopHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ cutSource bodyResult bodyPost,
    WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
    (bodyResult,bodyPost) = WordSemStateFiniteExact.evaluate body cutSource ∧
    wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
    ZeroSimulation ac (wordSemSTOP (.loop names body exitNames))
      (WordSemStateFiniteExact.decClock bodyPost)) ∧
  (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
    ZeroSimulation ac body cutSource)

theorem zeroEnterBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : Compiler.Backend.StackLang.HolProg width) (bodyResult : Option (WordSemResult width))
    (ih : ZeroLoopHypotheses ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (execution : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (notError : bodyResult ≠ some .error)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k) :
    ∃ compiledBody targetPost targetResult,
      compiled = .loop compiledBody ∧
      StackSemEvaluate.evaluate (compiledBody,target) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame cutSource bodyPost targetPost bodyResult targetResult lens := by
  rcases bodyComp : compNative ac false body (bs,n) (k,f,frame) with ⟨compiledBody,next⟩
  simp only [compNative,bodyComp,Prod.mk.injEq] at compilation
  obtain ⟨rfl,nextEq⟩ := compilation
  have cutRel := StateRelCutState.stateRelCutState ac k f frame source cutSource target lens names related cut
  have bodyConventions : postAllocConventionsHOL k body = true := by
    simp [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,callArgConventionHOL] at conventions ⊢
    exact ⟨conventions.1.1.2,conventions.2⟩
  have bodyFlat : flatExpConventions body = true := by simpa [flatExpConventions] using flat
  have bodyBound : maxVarHOL body < 2*frame+2*k := by
    simp only [maxVarHOL,max3HOL] at maxBound
    split at maxBound <;> split at maxBound <;> omega
  have bodyLabels : ∀ loc, StackSem.getLabelsExact compiledBody loc → StackSem.locCheckExact target.code loc := by
    simpa [StackSem.getLabelsExact] using labels
  have compilationBody : compNative ac false body (bs,n) (k,f,frame) = (compiledBody,(bsPost,nPost)) := by
    simpa [nextEq] using bodyComp
  obtain ⟨post,res,actual,resultRel⟩ := ih.2 cutSource cut k f frame bodyPost target
    bodyResult bs bsPost n nPost compiledBody lens
    ⟨execution,notError,cutRel,bodyConventions,bodyFlat,compilationBody,
      lengthBound,bitmapBound,bitmapPrefix,bodyLabels,bodyBound⟩
  exact ⟨compiledBody,post,res,rfl,actual,resultRel⟩

theorem zeroEnterRecursive {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalSource : WordSemStateFiniteExact width (Nat × C) F)
    (target targetBody : StackSemStateFiniteExact width C F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiledBody : Compiler.Backend.StackLang.HolProg width)
    (bodyResult finalResult : Option (WordSemResult width))
    (ih : ZeroLoopHypotheses ac names exitNames body source)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (sourceBody : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (continues : wordSemContLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (sourceRecursive : WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource))
    (notError : finalResult ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate (compiledBody,target) =
      (bodyResult.map compileResult,targetBody))
    (bodyConclusion : compCorrectResult ac k f frame cutSource bodyPost targetBody
      bodyResult (bodyResult.map compileResult) lens)
    (conventions : postAllocConventionsHOL k (.loop names body exitNames) = true)
    (flat : flatExpConventions (.loop names body exitNames) = true)
    (compilation : compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) =
      (.loop compiledBody,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact target.code loc)
    (maxBound : maxVarHOL (.loop names body exitNames) < 2*frame+2*k) :
    ∃ targetPost result,
      StackSemEvaluate.evaluate (.loop compiledBody,
        StackSemStateOps.decClock targetBody) =
        (result,targetPost) ∧
      compCorrectResult ac k f frame (WordSemStateFiniteExact.decClock bodyPost)
        finalSource targetPost finalResult result lens := by
  have recursiveIH := ih.1 cutSource bodyResult bodyPost ⟨cut,sourceBody.symm,continues,nonzero⟩
  have metadata := recursiveMetadata compiledBody target targetBody (bodyResult.map compileResult)
    0 (n-(appListAppend bs).length) (appListAppend bsPost) (by simpa using targetRun) bitmapBound bitmapPrefix labels
  have relation := recursiveRelation ac k f frame cutSource bodyPost targetBody lens bodyResult continues bodyConclusion
  apply recursiveIH k f frame finalSource (StackSemStateOps.decClock targetBody)
    finalResult bs bsPost n nPost (.loop compiledBody) lens
  simpa only [wordSemSTOP,StackSemStateOps.decClock] using
    (show WordSemStateFiniteExact.evaluate (.loop names body exitNames)
      (WordSemStateFiniteExact.decClock bodyPost) = (finalResult,finalSource) ∧
      finalResult ≠ some .error ∧ stateRel ac k f frame
        (WordSemStateFiniteExact.decClock bodyPost) (StackSemStateOps.decClock targetBody) lens 0 ∧
      postAllocConventionsHOL k (.loop names body exitNames) = true ∧
      flatExpConventions (.loop names body exitNames) = true ∧
      compNative ac false (.loop names body exitNames) (bs,n) (k,f,frame) = (.loop compiledBody,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ targetBody.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (targetBody.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc,StackSem.getLabelsExact (.loop compiledBody) loc → StackSem.locCheckExact targetBody.code loc) ∧
      maxVarHOL (.loop names body exitNames) < 2*frame+2*k from
      ⟨sourceRecursive,notError,relation,conventions,flat,compilation,lengthBound,
        metadata.1,metadata.2.1,metadata.2.2,maxBound⟩)

theorem zeroLoop {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : ZeroLoopHypotheses ac names exitNames body source) :
    ZeroSimulation ac (.loop names body exitNames) source := by
  classical
  intro k f frame finalSource target finalResult bs bsPost n nPost compiled lens premises
  rcases premises with ⟨sourceLoop,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases cut : WordSemStateFiniteExact.cutState (names,.ln) source with
  | none =>
    rw [WordSemStateFiniteExact.evaluate,cut] at sourceLoop
    have error : finalResult = some .error := congrArg Prod.fst sourceLoop.symm
    exact False.elim (notError error)
  | some cutSource =>
    rcases sourceBody : WordSemStateFiniteExact.evaluate body cutSource with ⟨bodyResult,bodyPost⟩
    have bodyError := bodyNonError names exitNames body source cutSource bodyPost finalSource
      bodyResult finalResult cut sourceBody sourceLoop notError
    obtain ⟨compiledBody,targetBody,targetResult,compiledEq,targetRun,bodyConclusion⟩ :=
      zeroEnterBody ac names exitNames body source cutSource bodyPost target k f frame lens
        bs bsPost n nPost compiled bodyResult ih cut sourceBody bodyError related conventions
        flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound
    subst compiled
    by_cases mismatch : bodyResult.map compileResult ≠ targetResult
    · have overflow := bodyOverflow ac k f frame names exitNames body source cutSource bodyPost
        finalSource target targetBody lens compiledBody 0 bodyResult finalResult targetResult
        related cut sourceBody sourceLoop (by simpa using targetRun) bodyConclusion mismatch
      exact ⟨targetBody,some (.halt (.word 2)),by simpa using overflow⟩
    · have resultEq : targetResult = bodyResult.map compileResult := (not_ne_iff.mp mismatch).symm
      subst targetResult
      have tailRun := sourceLoop
      rw [WordSemStateFiniteExact.evaluate,cut] at tailRun
      simp only [] at tailRun
      rw [WordSemStateFiniteExact.fix_clock_evaluate,sourceBody] at tailRun
      by_cases continues : wordSemContLoop bodyResult = true
      · have bodyRel := continuationRelation ac k f frame cutSource bodyPost targetBody lens
          bodyResult continues bodyConclusion
        have clocks := bodyRel.1
        have targetContinues : StackSemControl.contLoop (bodyResult.map compileResult) = true := by
          rw [contLoopCompile,continues]
        simp only [continues] at tailRun
        by_cases zero : bodyPost.clock = 0
        · simp only [zero] at tailRun
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj tailRun
          have targetZero : targetBody.clock = 0 := by omega
          exact ⟨StackSemStateOps.emptyEnv targetBody,some .timeOut,
            runLoopTimeout compiledBody target targetBody
              (bodyResult.map compileResult) targetRun targetContinues targetZero,
            timeoutRelation ac k f frame source bodyPost targetBody lens bodyRel⟩
        · simp only [zero] at tailRun
          obtain ⟨post,res,recursiveRun,recursiveConclusion⟩ :=
            zeroEnterRecursive ac names exitNames body source cutSource bodyPost finalSource target targetBody
              k f frame lens bs bsPost n nPost compiledBody bodyResult finalResult ih cut sourceBody
              continues zero (by simpa [wordSemSTOP] using tailRun) notError targetRun bodyConclusion
              conventions flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound
          have targetNonzero : targetBody.clock ≠ 0 := by omega
          have actual := runLoopRecursive compiledBody target
            targetBody post (bodyResult.map compileResult) res 0 targetRun targetContinues
            targetNonzero (by simpa using recursiveRun)
          have sourceHandler : source.handler = (WordSemStateFiniteExact.decClock bodyPost).handler := by
            have bodyHandler := LoopHandler.evaluateContLoopHandler body cutSource bodyPost bodyResult sourceBody continues
            have initialHandler := cutHandler names source cutSource cut
            simpa [WordSemStateFiniteExact.decClock] using initialHandler.trans bodyHandler.symm
          refine ⟨post,res,?_,?_⟩
          · simpa [Nat.add_assoc] using actual
          · exact originRelation ac k f frame source (WordSemStateFiniteExact.decClock bodyPost)
              finalSource post lens finalResult res sourceHandler recursiveConclusion
      · simp only [continues] at tailRun
        by_cases breakZero : bodyResult = some (.break 0)
        · subst bodyResult
          cases exitCut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost with
          | none =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            contradiction
          | some exitPost =>
            simp [exitCut] at tailRun
            obtain ⟨rfl,rfl⟩ := tailRun
            exact ⟨targetBody,none,
              runLoopBreakZero compiledBody target targetBody targetRun,
              breakZeroRelation ac k f frame source cutSource bodyPost exitPost targetBody lens exitNames
                bodyConclusion exitCut⟩
        · have sourceExit : (wordSemExitLoop bodyResult,bodyPost) = (finalResult,finalSource) := by
            cases bodyResult with
            | none => exact tailRun
            | some result =>
              cases result <;> try exact tailRun
              next depth => cases depth <;> simp_all
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj sourceExit
          have targetExits : StackSemControl.contLoop (bodyResult.map compileResult) = false := by
            rw [contLoopCompile]
            cases h : wordSemContLoop bodyResult <;> simp_all
          have exitEq : StackSemControl.exitLoop (bodyResult.map compileResult) =
              (wordSemExitLoop bodyResult).map compileResult := by
            rw [exitLoopCompile]
            cases bodyResult with
            | none => rfl
            | some result =>
              cases result <;> simp_all
          refine ⟨targetBody,(wordSemExitLoop bodyResult).map compileResult,?_,?_⟩
          · rw [← exitEq]
            exact runLoopExit compiledBody target
              targetBody (bodyResult.map compileResult) targetRun targetExits
          · exact exitRelation ac k f frame source cutSource bodyPost targetBody lens bodyResult
              (cutHandler names source cutSource cut) bodyConclusion

theorem zeroSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac .skip source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨target, none, ?_, ?_⟩
  · simp only [StackSemEvaluate.evaluate_skip]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem zeroBreak {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.break label) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨target, some (.break label), ?_, ?_⟩
  · simp only [StackSemEvaluate.evaluate_break]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem zeroContinue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.continue label) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨target, some (.continue label), ?_, ?_⟩
  · simp only [StackSemEvaluate.evaluate_continue]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem zeroTick {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac .tick source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have related := premises.2.2.1
  have clocks : source.clock = target.clock := by
    unfold stateRel at related
    exact related.1
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  subst compiled
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  by_cases zero : source.clock = 0
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨StackSemStateOps.emptyEnv target, some .timeOut, ?_, ?_⟩
    · rw [StackSemEvaluate.evaluate_tick, if_pos (clocks.symm.trans zero)]
    · simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
        not_true_eq_false, ↓reduceIte]
      exact ⟨related.2.2.2.1.symm, clocks⟩
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨StackSemStateOps.decClock target, none, ?_, ?_⟩
    · have targetNonzero : target.clock ≠ 0 := fun h => zero (clocks.trans h)
      rw [StackSemEvaluate.evaluate_tick, if_neg targetNonzero]
    · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
      exact Clock.stateRelDecClock ac k f frame source target lens 0 related

theorem zeroGet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.get register name) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  cases read : WordSemStateFiniteExact.getStore name source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have storeRel : source.store = target.store.eraseEq .handler :=
      related.2.2.2.2.2.2.2.2.2.2.2.1
    have targetRead : target.store.lookup (StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name)) = some value := by
      unfold WordSemStateFiniteExact.getStore at read
      rw [storeRel] at read
      cases name <;>
        simp only [storeNameOfWord,StackSemRegisterTransfers.storeOfSyntax,
          HolFiniteMapExact.eraseEq,FDOMSUB_HOL] at read ⊢ <;>
        simp only [reduceCtorEq,ite_false,ite_true] at read <;>
        exact read
    have useStore : target.useStore = true := related.2.2.2.2.2.1
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.get r (storeNameOfWord name),target) =
        (none,StackSemStateOps.setVar r value target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_get,useStore,targetRead]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens value (fun r => .get r (storeNameOfWord name))
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨post,none,?_,?_⟩
    · simpa only [← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

theorem zeroLocValue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register location : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.locValue register location) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  by_cases present : sptMem location source.code
  swap
  · simp [present] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  · simp only [present,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have codeDomain : sptDomain target.code =
        (fun n => n=raiseStubLocation ∨ n=storeConstsStubLocation ∨ sptDomain source.code n) :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have valid : StackSem.locCheckExact target.code (location,0) := by
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change sptDomain target.code location
      rw [codeDomain]
      exact Or.inr (Or.inr present)
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.locValue r location 0,target) =
        (none,StackSemStateOps.setVar r (.loc location 0) target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_locValue,valid]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens (.loc location 0) (fun r => .locValue r location 0)
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨post,none,?_,?_⟩
    · simpa only [← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

theorem zeroSet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : WordStoreHOL)
    (expression : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.set name expression) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases expression <;> simp [flatExpConventions] at flat
  rename_i register
  simp only [WordSemStateFiniteExact.evaluate] at execution
  have notHandler : name ≠ .handler := by
    intro eq; subst name; simp only [true_or,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  have notBitmap : name ≠ .bitmapBase := by
    intro eq; subst name; simp only [or_true,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  simp only [notHandler,notBitmap,false_or,if_false,WordSemStateFiniteExact.wordExp] at execution
  cases read : WordSemStateFiniteExact.getVar register source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,everyVarExpHOL,isPhyVar] using conventions
    rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k,f,frame) with ⟨loads,reg⟩
    obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register reg loads
        source target lens value format even read related
    have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
    have codec : StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name) = name := by
      cases name <;> rfl
    have programEq := congrArg Prod.fst compilation
    have compiledEq : compiled = wStackLoadNative loads (.set (storeNameOfWord name) reg) := by
      cases name <;> simp only [compNative,format] at programEq <;>
        first | exact programEq.symm | contradiction
    subst compiled
    refine ⟨StackSemStateOps.setStore name value loaded,none,?_,?_⟩
    · simp only [LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq,loadRun]
      have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
        have le : loaded.clock ≤ target.clock := by omega
        simp only [StackSemControl.fixClock,Nat.min_eq_right le]
      rw [fix]
      simp only [StackSemEvaluate.evaluate_set,useStore,not_true_eq_false,if_false,
        loadedRead,codec]
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte] using StateRelStoreUpdate.stateRelSetStore ac k f frame source
          loaded lens 0 name value notHandler loadRel

theorem zeroCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.codeBufferWrite r1 r2) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    CodeBufferWrite.sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.codeBuffer = source.codeBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨{t2 with codeBuffer := cb},none,?_,?_⟩
  · simp only [wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using CodeBufferWrite.codeBufferRelation cb rel2


theorem zeroDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.dataBufferWrite r1 r2) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    DataBufferWrite.sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.dataBuffer = source.dataBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have capacity : cb.buffer.length+cb.spaceLeft = source.dataBuffer.buffer.length+source.dataBuffer.spaceLeft := by
    unfold wordSemBufferWrite at writeEq
    split at writeEq
    · rename_i guard
      have equal := Option.some.inj writeEq
      subst cb
      simp only [List.length_append,List.length_singleton]
      omega
    · cases writeEq
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨{t2 with dataBuffer := cb},none,?_,?_⟩
  · simp only [wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    have useStack : t2.useStack = true := rel2.2.2.2.2.1
    simp only [StackSemEvaluate.evaluate_dataBufferWrite,useStack,not_true_eq_false,if_false,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using DataBufferWrite.dataBufferRelation cb capacity rel2


theorem zeroFFI {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (index : Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.ffi index ptr1 len1 ptr2 len2 names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, rfl, rfl, hc1, hc2⟩ :=
    FFI.ffiConventions k index ptr1 len1 ptr2 len2 names conventions
  simp only [compNative, Prod.mk.injEq] at compilation
  obtain ⟨rfl, -⟩ := compilation
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := related'
  have hvar : ∀ m v, WordSemStateFiniteExact.getVar (2 * m) source = some v → m < k →
      StackSemStateOps.getVar m target = some v := by
    intro m v hm hlt
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 (2 * m) v
      ⟨related, hm, by omega, by omega⟩
    rwa [show 2 * m / 2 = m by omega] at this
  rw [WordSemStateFiniteExact.evaluate] at execution
  rw [StackSemEvaluate.evaluate_ffi]
  simp only [show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl,
    show (6 : Nat) / 2 = 3 by rfl, show (8 : Nat) / 2 = 4 by rfl]
  rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w | ⟨_, _⟩) <;>
    rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h8 : WordSemStateFiniteExact.getVar 8 source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h6 : WordSemStateFiniteExact.getVar 6 source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h4, h2, h8, h6, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rw [hvar 2 _ h4 (by omega), hvar 1 _ h2 (by omega), hvar 4 _ h8 (by omega),
    hvar 3 _ h6 (by omega)]
  simp only [r8, r9, r15, r4]
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases hr1 : readBytearrayWordHOL w2 w.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes <;>
    rcases hr2 : readBytearrayWordHOL w4 w3.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes2 <;>
    simp only [hr1, hr2, Prod.mk.injEq] at execution ⊢ <;>
    try exact absurd execution.1.symm notError
  rcases hcall : callFFIHOL source.ffi (.extCall index) bytes bytes2 with ⟨newFfi, newBytes⟩ | outcome <;>
    simp only [hcall, Prod.mk.injEq] at execution ⊢ <;> obtain ⟨rfl, rfl⟩ := execution
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
    have henv : env = sptUnion (sptInter source.locals names.2) (sptInter source.locals names.1) := by
      unfold wordSemCutEnv at hce
      rcases hcs : wordSemCutEnvs names source.locals with _ | ⟨e1, e2⟩
      · rw [hcs] at hce; cases hce
      rw [hcs] at hce
      obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcs
      simp only [Option.some.injEq] at hce he1 he2
      rw [← hce, ← he1, ← he2]
    unfold stateRel
    refine ⟨r1, r2, r3, rfl, r5, r6, r7, rfl, rfl, r10, r11, r12, r13, r14, rfl, rfl, r17, rfl,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      ?_, r37, r38, ?_⟩
    · show sptWf env = true
      rw [henv]
      exact sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩
    · intro m v hm
      change sptLookup m env = some v at hm
      rw [henv, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at hm
      have hlook : sptLookup m source.locals = some v ∧
          (sptDomain names.1 m ∨ sptDomain names.2 m) := by
        unfold sptDomain
        revert hm
        cases sptLookup m source.locals <;> cases sptLookup m names.2 <;>
          cases sptLookup m names.1 <;> simp
      obtain ⟨hl, hd⟩ := hlook
      have hev : m % 2 = 0 ∧ 2 * k ≤ m := hd.elim (hc1 m) (hc2 m)
      obtain ⟨he, hif⟩ := rloc m v hl
      refine ⟨he, ?_⟩
      rw [if_neg (by omega)] at hif ⊢
      exact hif
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
    exact ⟨r4.symm, r1⟩

private theorem heapSourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (operator : HolBinop) (dst src : Nat) (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.opCurrHeap operator dst src) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ operand heap value : BitVec width,
      WordSemStateFiniteExact.getVar src source = some (.word operand) ∧
      source.store.lookup .currHeap = some (.word heap) ∧
      wordOpHOL operator [operand,heap] = some value ∧
      result = none ∧ post = WordSemStateFiniteExact.setVar dst (.word value) source := by
  cases read : WordSemStateFiniteExact.getVar src source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
      read,theWords] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some operandValue =>
    cases operandValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
        read,theWords] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word operand =>
      cases heapRead : source.store.lookup .currHeap with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some heapValue =>
        cases heapValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word heap =>
          cases operation : wordOpHOL operator [operand,heap] with
          | none =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction
          | some value =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨operand,heap,value,rfl,rfl,operation,rfl,rfl⟩

theorem zeroOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.opCurrHeap operator dst src) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨operand,heap,value,read,heapRead,operation,rfl,rfl⟩ :=
    heapSourceSuccess source sourcePost operator dst src result execution notError
  have evens : dst % 2 = 0 ∧ src % 2 = 0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  have dstEq : dst = 2*(dst/2) := by omega
  have bound : dst/2 < frame+k := by
    simp only [maxVarHOL] at maxBound
    omega
  rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 src (k,f,frame) with ⟨loads,reg⟩
  obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame src reg loads
      source target lens (.word operand) format evens.2 read related
  have storeEq : source.store = loaded.store.eraseEq .handler :=
    loadRel.2.2.2.2.2.2.2.2.2.2.2.1
  have targetHeap : loaded.store.lookup .currHeap = some (.word heap) := by
    rw [storeEq] at heapRead
    simpa [HolFiniteMapExact.eraseEq,FDOMSUB_HOL] using heapRead
  have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
  have callback : ∀ d, d ≤ k →
      StackSemEvaluate.evaluate (.opCurrHeap operator d reg,loaded) =
        (none,StackSemStateOps.setVar d (.word value) loaded) := by
    intro d _
    change loaded.regs.lookup reg = some (.word operand) at loadedRead
    simp [StackSemEvaluate.evaluate_opCurrHeap,useStore,StackSemExpressions.wordExp,
      loadedRead,targetHeap,operation]
  obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
    (dst/2) source loaded lens (.word value) (fun d => .opCurrHeap operator d reg)
    loadRel bound callback
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,format] at programEq
  subst compiled
  refine ⟨post,none,?_,?_⟩
  · simp only [LoadRegister.evaluateWStackLoadSeq,
      StackSemEvaluate.evaluate_seq,loadRun]
    have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
      have le : loaded.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix]
    simpa only [← dstEq] using actual
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,← dstEq] using postRel

theorem zeroMove {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.move priority moves) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨values,distinct,reads,rfl,rfl⟩ :=
    Move.sourceSuccess priority moves source sourcePost result execution notError
  have evens : (∀ n ∈ moves.map Prod.fst, n % 2=0) ∧
      (∀ n ∈ moves.map Prod.snd, n % 2=0) := by
    have raw : (∀ a b, (a,b) ∈ moves → a % 2=0) ∧
        (∀ a b, (a,b) ∈ moves → b % 2=0) := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar,List.all_eq_true] using conventions
    constructor
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.1 a b input
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.2 a b input
  have wf : sptWf source.locals=true := by
    unfold stateRel at related
    tauto
  obtain ⟨post,run,relation,_,_⟩ := Move.actualScheduledRun ac k f frame lens moves source target
    related distinct evens.1 evens.2 (by simp [reads]) (by simpa [maxVarHOL] using maxBound)
  rw [Move.scheduledSourceStateReconstruction moves source target k values distinct
    evens.1 evens.2 reads wf] at relation
  have program := congrArg Prod.fst compilation
  simp only [compNative] at program
  subst compiled
  refine ⟨post,none,?_,?_⟩
  · exact run
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,↓reduceIte] using relation

theorem zeroInstall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ZeroSimulation ac (.install ptr len dptr dlen names) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, hd3, hd4, hc1, hc2⟩ :=
    Install.installConventions k ptr len dptr dlen names conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 dptr (k, f, frame) with ⟨xs, reg3⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 dlen (k, f, frame) with ⟨ys, reg4⟩
  have programEq := congrArg Prod.fst compilation
  simp only [compNative, fmt1, fmt2] at programEq
  subst compiled
  -- The source run.
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w1 | ⟨_, _⟩) <;>
    rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h3 : WordSemStateFiniteExact.getVar dptr source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h5 : WordSemStateFiniteExact.getVar dlen source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h2, h4, h3, h5, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hor : source.compileOracle 0 with ⟨⟨bm0, cfg⟩, progs⟩
  simp only [hor] at execution
  rcases hcf : wordSemBufferFlush source.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
    rcases hdf : wordSemBufferFlush source.dataBuffer w3 w4 with _ | ⟨data, db⟩ <;>
    simp only [hcf, hdf, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hsc : source.compile (bm0, cfg) progs with _ | ⟨bytes', data', cfg'⟩ <;>
    rcases progs with _ | ⟨⟨kk, argc, prog⟩, rest⟩ <;>
    simp only [hsc, Prod.mk.injEq] at execution <;>
    try first
      | exact absurd execution.1.symm notError
      | exact absurd (congrArg Prod.fst execution).symm notError
  by_cases hcond : bytes = bytes' ∧ data = data' ∧
      (holShiftSeq 1 source.compileOracle 0).1 = cfg'
  swap
  · rw [if_neg hcond] at execution
    exact absurd (congrArg Prod.fst execution).symm notError
  rw [if_pos hcond] at execution
  simp only [Prod.mk.injEq] at execution
  obtain ⟨rfl, rfl⟩ := execution
  -- The target loads of the data pointer and length.
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame dptr reg3 xs source target lens
      (.word w3) fmt1 hd3 h3 related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame dlen reg4 ys source t1 lens
      (.word w4) fmt2 hd4 h5 rel1
  have r10 : 4 < k := rel2.2.2.2.2.2.2.2.2.2.1
  have read1 : StackSemStateOps.getVar 1 t2 = some (.word w1) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 2 _
      ⟨rel2, h2, rfl, by omega⟩
    simpa using this
  have read2 : StackSemStateOps.getVar 2 t2 = some (.word w2) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 4 _
      ⟨rel2, h4, rfl, by omega⟩
    simpa using this
  have read3 : StackSemStateOps.getVar reg3 t2 = some (.word w3) := by
    rw [otherReads reg3 regNe]; exact loaded1
  -- The target compiler and oracle on the installed programs.
  have rel2' := rel2
  unfold stateRel at rel2'
  obtain ⟨-, -, -, -, r5, -, -, -, -, -, -, -, -, -, -, -, -, -, r19, r20, r21, r22, -⟩ := rel2'
  rcases hcw : compileWordToStackNative ac false k ((kk, argc, prog) :: rest) (.nil, bm0) with
    ⟨progs2, fs, bm⟩
  have hsc' := hsc
  rw [r21] at hsc'
  simp only [hcw] at hsc'
  rcases htc : t2.compile cfg progs2 with _ | ⟨bytes2, cfg2⟩
  · simp [htc] at hsc'
  simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc'
  obtain ⟨rfl, rfl, rfl⟩ := hsc'
  have hor2 : t2.compileOracle 0 = (cfg, progs2, appListAppend bm.1) := by
    rw [r22]; simp only [hor, hcw]
  have hmap := mapFstCompileWordToStack ac false k _ _ _ _ hcw
  rcases progs2 with _ | ⟨⟨kk2, prog2⟩, rest2⟩
  · simp at hmap
  simp only [List.map_cons, List.cons.injEq] at hmap
  obtain ⟨rfl, -⟩ := hmap
  have hflush : wordSemBufferFlush source.dataBuffer w3 w4 = some (data, db) := hdf
  have hdata : source.dataBuffer.buffer = appListAppend bm.1 := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [hflush.1, hcond.2.1]
    · cases hflush
  have hdb : db.buffer = [] ∧ db.spaceLeft = source.dataBuffer.spaceLeft := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [← hflush.2]; exact ⟨rfl, rfl⟩
    · cases hflush
  have hcfg : (source.compileOracle 1).1 = (bm.2, cfg2) := hcond.2.2
  have hnew : (holShiftSeq 1 t2.compileOracle 0).1 = cfg2 := by
    show (t2.compileOracle 1).1 = cfg2
    rcases hso : source.compileOracle 1 with ⟨⟨b1, c1⟩, ps⟩
    rw [r22]
    simp only [hso]
    rw [hso] at hcfg
    simp only [Prod.mk.injEq] at hcfg
    rcases compileWordToStackNative ac false k ps (.nil, b1) with ⟨a, b, c⟩
    exact hcfg.2
  -- The target run and the related post-states.
  refine ⟨{ t2 with
      bitmaps := t2.bitmaps ++ appListAppend bm.1
      codeBuffer := cb
      dataBuffer := db
      code := sptUnion t2.code (sptFromAList ((kk2, prog2) :: rest2))
      regs := (StackSemStateOps.restrictIn t2.regs t2.ffiSaveRegs).updateEq (1, .loc kk2 0)
      fpRegs := HolFiniteMapExact.empty
      compileOracle := holShiftSeq 1 t2.compileOracle }, none, ?_, ?_⟩
  · simp only [wStackLoadAppend, Function.comp_apply,
      show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)), t1) =
        (none, t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)), t2) =
        (none, t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix2]
    rw [StackSemEvaluate.evaluate_install]
    simp only [read1, read2, read3, loaded2, hor2, r20, r19, r5, hcf, hflush, if_true, htc]
    rw [if_pos ⟨hcond.1, hcond.2.1.trans (congrArg (fun x => x.2.2) hor2).symm, hnew⟩]
  · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
    exact Install.installRelation ac k f frame source t2 lens rel2 names hc1 hc2 env hce bm0 cfg kk2 argc
      prog rest hor (_ :: rest2) fs bm hcw cfg2 hcfg cb db hdata hdb


/-- Programs built from instructions, sequences, conditionals and loops. -/
inductive LoopBlock {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | inst (i) : LoopBlock (.inst i)
  | install (ptr len dptr dlen names) : LoopBlock (.install ptr len dptr dlen names)
  | move (priority moves) : LoopBlock (.move priority moves)
  | opCurrHeap (op dst src) : LoopBlock (.opCurrHeap op dst src)
  | ffi (index ptr1 len1 ptr2 len2 names) : LoopBlock (.ffi index ptr1 len1 ptr2 len2 names)
  | set (name expression) : LoopBlock (.set name expression)
  | codeBufferWrite (r1 r2) : LoopBlock (.codeBufferWrite r1 r2)
  | dataBufferWrite (r1 r2) : LoopBlock (.dataBufferWrite r1 r2)
  | get (register name) : LoopBlock (.get register name)
  | locValue (register location) : LoopBlock (.locValue register location)
  | skip : LoopBlock .skip
  | tick : LoopBlock .tick
  | break (label) : LoopBlock (.break label)
  | continue (label) : LoopBlock (.continue label)
  | seq {a b} : LoopBlock a → LoopBlock b → LoopBlock (.seq a b)
  | ite (cmp r ri) {a b} : LoopBlock a → LoopBlock b → LoopBlock (.ite cmp r ri a b)
  | loop (names exitNames) {body} : LoopBlock body → LoopBlock (.loop names body exitNames)

/-- Zero-extra-clock correctness holds for every execution of a loop block. -/
theorem loopBlock_zero {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (p : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width (Nat × C) F),
      LoopBlock p → ZeroSimulation ac p source := by
  apply WordSemStateFiniteExact.evaluate_ind
    (fun p source => LoopBlock p → ZeroSimulation ac p source)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try { intros; rename_i h; cases h <;> done }
  case refine_21 => intro ptr len dptr dlen names source _; exact zeroInstall ac ptr len dptr dlen names source
  case refine_4 => intro priority moves source _; exact zeroMove ac priority moves source
  case refine_24 => intro index ptr1 len1 ptr2 len2 names source _; exact zeroFFI ac index ptr1 len1 ptr2 len2 names source
  case refine_9 => intro op dst src source _; exact zeroOpCurrHeap ac op dst src source
  case refine_8 => intro name expression source _; exact zeroSet ac name expression source
  case refine_22 => intro r1 r2 source _; exact zeroCodeBufferWrite ac r1 r2 source
  case refine_23 => intro r1 r2 source _; exact zeroDataBufferWrite ac r1 r2 source
  case refine_7 => intro register name source _; exact zeroGet ac register name source
  case refine_20 => intro register location source _; exact zeroLocValue ac register location source
  case refine_1 => intro source _; exact zeroSkip ac source
  case refine_11 => intro source _; exact zeroTick ac source
  case refine_16 => intro label source _; exact zeroBreak ac label source
  case refine_17 => intro label source _; exact zeroContinue ac label source
  case refine_5 =>
    intro inst source block k f frame sourcePost target result bs bsPost n nPost compiled lens premises
    obtain ⟨post, out, run, related, _⟩ :=
      inst_zeroClock ac inst source sourcePost target result k f frame bs bsPost n nPost compiled lens premises
    exact ⟨post, out, run, related⟩
  case refine_13 =>
    intro a b source ih block
    cases block with
    | seq ha hb =>
      apply zeroSeq ac a b source (ih.2 ha)
      intro result middle hrun
      exact ih.1 result middle hrun hb
  case refine_18 =>
    intro cmp r ri a b source ih block
    cases block with
    | ite _ _ _ ha hb =>
      apply zeroIf ac cmp r ri a b source
      constructor
      · intro v3 v4 x y v guard
        exact ih.1 v3 v4 x y v guard ha
      · intro v3 v4 x y v guard
        exact ih.2 v3 v4 x y v guard hb
  case refine_19 =>
    intro names body exitNames source ih block
    cases block with
    | loop _ _ hb =>
      apply zeroLoop ac names exitNames body source
      constructor
      · intro cut result post guard
        exact ih.1 cut result post guard (.loop names exitNames hb)
      · intro cut guard
        exact ih.2 cut guard hb


theorem loopBlock_loop {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (block : LoopBlock p) : loopWord p = true := by
  induction block with
  | inst i => rfl
  | install ptr len dptr dlen names => rfl
  | move priority moves => rfl
  | opCurrHeap op dst src => rfl
  | ffi index ptr1 len1 ptr2 len2 names => rfl
  | set name expression => rfl
  | codeBufferWrite r1 r2 => rfl
  | dataBufferWrite r1 r2 => rfl
  | get register name => rfl
  | locValue register location => rfl
  | skip => rfl
  | tick => rfl
  | «break» label => rfl
  | «continue» label => rfl
  | seq ha hb iha ihb => simp [loopWord, iha, ihb]
  | ite cmp r ri ha hb iha ihb => simp [loopWord, iha, ihb]
  | loop names exits hb ih => simp [loopWord, ih]

/-- Loop-block execution preserves the compiler result relation at a clock
bounded by source steps, and has a computable target-step bound. -/
theorem loopBlock_normalized {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width)) (block : LoopBlock p)
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
      StackSteps.steps (compiled, {target with clock := limit}) ≤ StackAllocSteps.loopOnlyCost limit compiled := by
  have frag := loopBlock_loop block
  have normalized := loopWord_normalized_run p source sourcePost result limit frag
    premises.1 notTimeout stepsBound
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have simulation := loopBlock_zero (C := C) (F := F) ac p {source with clock := limit} block
  obtain ⟨post, out, run, conclusion⟩ := simulation k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)}
    {target with clock := limit} result bs bsPost n nPost compiled lens
    ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have shape := loopWord_compiled ac p frag (bs, n) (k, f, frame)
  rw [premises.2.2.2.2.2.1] at shape
  exact ⟨post, out, run, conclusion, StackAllocSteps.loopOnlyCostBound limit compiled shape _ (Nat.le_refl _)⟩



end SteppedFlapjack.WordToStackSteps
