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

/-- Programs built from instructions, sequences, conditionals and loops. -/
inductive LoopBlock {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | inst (i) : LoopBlock (.inst i)
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
