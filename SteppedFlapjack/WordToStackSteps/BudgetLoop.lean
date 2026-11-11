import SteppedFlapjack.WordToStackSteps.BudgetSimulation
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Loop
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
private theorem bodyNonTimeout {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalPost : WordSemStateFiniteExact width C F)
    (bodyResult finalResult : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (bodyRun : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (loopRun : WordSemStateFiniteExact.evaluate (.loop names body exitNames) source = (finalResult,finalPost))
    (notTimeout : finalResult ≠ some .timeOut) : bodyResult ≠ some .timeOut := by
  intro timeout
  subst bodyResult
  rw [WordSemStateFiniteExact.evaluate,cut] at loopRun
  simp only [] at loopRun
  rw [WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at loopRun
  simp [wordSemContLoop,wordSemExitLoop] at loopRun
  obtain ⟨rfl,rfl⟩ := loopRun
  contradiction

private theorem budgetEnterBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (k f frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : Compiler.Backend.StackLang.HolProg width) (bodyResult : Option (WordSemResult width))
    (bodyCost reserve : Nat)
    (ih : ∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
      BudgetSimulation ac body cutSource bodyCost)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (execution : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (notError : bodyResult ≠ some .error) (notTimeout : bodyResult ≠ some .timeOut)
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
      StackSemEvaluate.evaluate (compiledBody,{target with clock := target.clock + bodyCost + reserve}) = (targetResult,targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (bodyPost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ bodyPost.clock + bodyCost + reserve)) ∧
      compCorrectResult ac k f frame cutSource bodyPost {targetPost with clock := bodyPost.clock} bodyResult targetResult lens := by
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
  obtain ⟨post,res,actual,enough,accounting,resultRel⟩ := ih cutSource cut k f frame bodyPost target
    bodyResult bs bsPost n nPost compiledBody lens
    ⟨execution,notError,notTimeout,cutRel,bodyConventions,bodyFlat,compilationBody,
      lengthBound,bitmapBound,bitmapPrefix,bodyLabels,bodyBound⟩ reserve
  exact ⟨compiledBody,post,res,rfl,actual,enough,accounting,resultRel⟩



/-- Explicit body and remaining-iteration allowances for one reached loop state. -/
def BudgetLoopHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (bodyCost recCost : Nat) : Prop :=
  (∀ cutSource bodyResult bodyPost,
    WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource ∧
    (bodyResult,bodyPost) = WordSemStateFiniteExact.evaluate body cutSource ∧
    wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
    BudgetSimulation ac (wordSemSTOP (.loop names body exitNames))
      (WordSemStateFiniteExact.decClock bodyPost) recCost) ∧
  (∀ cutSource, WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource →
    BudgetSimulation ac body cutSource bodyCost)

/-- Loop iterations compose their explicit body and remaining-iteration budgets. -/
theorem budgetLoop {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (names exitNames : Spt Unit)
    (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (bodyCost recCost : Nat)
    (ih : BudgetLoopHypotheses ac names exitNames body source bodyCost recCost) :
    BudgetSimulation ac (.loop names body exitNames) source (bodyCost + recCost) := by
  classical
  intro k f frame finalSource target finalResult bs bsPost n nPost compiled lens premises reserve
  rcases premises with ⟨sourceLoop,notError,notTimeout,related,conventions,flat,compilation,
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
    have bodyTimeout := bodyNonTimeout names exitNames body source cutSource bodyPost finalSource
      bodyResult finalResult cut sourceBody sourceLoop notTimeout
    obtain ⟨compiledBody,targetBody,targetResult,compiledEq,targetRun,bodyEnough,bodyAccounting,bodyConclusion⟩ :=
      budgetEnterBody ac names exitNames body source cutSource bodyPost target k f frame lens
        bs bsPost n nPost compiled bodyResult bodyCost (recCost+reserve) ih.2 cut sourceBody bodyError bodyTimeout related conventions
        flat compilation lengthBound bitmapBound bitmapPrefix labels maxBound
    subst compiled
    by_cases mismatch : bodyResult.map compileResult ≠ targetResult
    · have bodyUnnormalized : compCorrectResult ac k f frame cutSource bodyPost targetBody
          bodyResult targetResult lens := by
        unfold compCorrectResult at bodyConclusion ⊢
        rw [if_pos mismatch] at bodyConclusion ⊢
        exact bodyConclusion
      have overflow := bodyOverflow ac k f frame names exitNames body source cutSource bodyPost
        finalSource target targetBody lens compiledBody (bodyCost+(recCost+reserve)) bodyResult finalResult targetResult
        related cut sourceBody sourceLoop (by simpa [Nat.add_assoc] using targetRun) bodyUnnormalized mismatch
      refine ⟨targetBody,some (.halt (.word 2)),?_,by omega,Or.inl rfl,?_⟩
      · simpa [Nat.add_assoc] using overflow.1
      · simpa using compCorrectResult_setClocks ac k f frame source finalSource targetBody finalResult
          (some (.halt (.word 2))) lens finalSource.clock overflow.2
    · have resultEq : targetResult = bodyResult.map compileResult := (not_ne_iff.mp mismatch).symm
      subst targetResult
      have dimension : goodDimindex width := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have bodyNotLimit : bodyResult.map compileResult ≠ some (.halt (.word 2)) := by
        cases bodyResult with
        | none => simp
        | some r =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact Ne.symm ((haltEqCompileResult r).2 dimension)
      have ⟨bodyLower,bodyUpper⟩ := bodyAccounting.resolve_left bodyNotLimit
      have tailRun := sourceLoop
      rw [WordSemStateFiniteExact.evaluate,cut] at tailRun
      simp only [] at tailRun
      rw [WordSemStateFiniteExact.fix_clock_evaluate,sourceBody] at tailRun
      by_cases continues : wordSemContLoop bodyResult = true
      · simp only [continues] at tailRun
        by_cases zero : bodyPost.clock = 0
        · simp only [zero] at tailRun
          have timeout : finalResult = some .timeOut := congrArg Prod.fst tailRun.symm
          exact (notTimeout timeout).elim
        · simp only [zero] at tailRun
          have bodyRel := continuationRelation ac k f frame cutSource bodyPost
            {targetBody with clock := bodyPost.clock} lens bodyResult continues bodyConclusion
          have targetContinues : StackSemControl.contLoop (bodyResult.map compileResult) = true := by
            rw [contLoopCompile,continues]
          have metadata := recursiveMetadata compiledBody target targetBody (bodyResult.map compileResult)
            (bodyCost+(recCost+reserve)) (n-(appListAppend bs).length) (appListAppend bsPost)
            (by simpa [Nat.add_assoc] using targetRun) bitmapBound bitmapPrefix labels
          have relation := recursiveRelation ac k f frame cutSource bodyPost
            {targetBody with clock := bodyPost.clock} lens bodyResult continues bodyConclusion
          let remaining := targetBody.clock - bodyPost.clock - recCost
          have remainingLower : reserve ≤ remaining := by dsimp [remaining]; omega
          have remainingUpper : recCost + remaining ≤ bodyCost + recCost + reserve := by dsimp [remaining]; omega
          have remainingEq : bodyPost.clock - 1 + recCost + remaining = targetBody.clock - 1 := by dsimp [remaining]; omega
          have recursiveIH := ih.1 cutSource bodyResult bodyPost ⟨cut,sourceBody.symm,continues,zero⟩
          obtain ⟨post,res,recursiveRun,postEnough,accounting,recursiveConclusion⟩ :=
            recursiveIH k f frame finalSource (StackSemStateOps.decClock {targetBody with clock := bodyPost.clock})
              finalResult bs bsPost n nPost (.loop compiledBody) lens
              ⟨by simpa [wordSemSTOP] using tailRun, notError, notTimeout, relation, conventions, flat,
                compilation, lengthBound, metadata.1, metadata.2.1, metadata.2.2, maxBound⟩ remaining
          have actualRec : StackSemEvaluate.evaluate (.loop compiledBody,StackSemStateOps.decClock targetBody) = (res,post) := by
            simpa only [StackSemStateOps.decClock, remainingEq] using recursiveRun
          have targetNonzero : targetBody.clock ≠ 0 := by omega
          have actual := runLoopRecursive compiledBody
            {target with clock := target.clock + bodyCost + (recCost+reserve)}
            targetBody post (bodyResult.map compileResult) res 0 targetRun targetContinues
            targetNonzero (by simpa using actualRec)
          have sourceHandler : source.handler = (WordSemStateFiniteExact.decClock bodyPost).handler := by
            have bodyHandler := LoopHandler.evaluateContLoopHandler body cutSource bodyPost bodyResult sourceBody continues
            have initialHandler := cutHandler names source cutSource cut
            simpa [WordSemStateFiniteExact.decClock] using initialHandler.trans bodyHandler.symm
          refine ⟨post,res,?_,by omega,?_,?_⟩
          · simpa [Nat.add_assoc] using actual
          · rcases accounting with limit | ⟨lower,upper⟩
            · exact Or.inl limit
            · right; constructor <;> omega
          · exact originRelation ac k f frame source (WordSemStateFiniteExact.decClock bodyPost)
              finalSource {post with clock := finalSource.clock} lens finalResult res sourceHandler recursiveConclusion
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
            have clocks := WordSemStateFiniteExact.cutState_clock_termdep _ _ _ exitCut
            have relation := breakZeroRelation ac k f frame source cutSource bodyPost exitPost
              {targetBody with clock := bodyPost.clock} lens exitNames bodyConclusion exitCut
            refine ⟨targetBody,none,?_,by omega,?_,?_⟩
            · simpa [Nat.add_assoc] using runLoopBreakZero compiledBody
                {target with clock := target.clock + bodyCost + (recCost+reserve)} targetBody targetRun
            · right; constructor <;> omega
            · simpa only [show exitPost.clock = bodyPost.clock by omega] using relation
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
            | some result => cases result <;> simp_all
          refine ⟨targetBody,(wordSemExitLoop bodyResult).map compileResult,?_,by omega,?_,?_⟩
          · rw [← exitEq]
            simpa [Nat.add_assoc] using runLoopExit compiledBody
              {target with clock := target.clock + bodyCost + (recCost+reserve)}
              targetBody (bodyResult.map compileResult) targetRun targetExits
          · right; constructor <;> omega
          · exact exitRelation ac k f frame source cutSource bodyPost {targetBody with clock := bodyPost.clock} lens bodyResult
              (cutHandler names source cutSource cut) bodyConclusion

end SteppedFlapjack.WordToStackSteps
