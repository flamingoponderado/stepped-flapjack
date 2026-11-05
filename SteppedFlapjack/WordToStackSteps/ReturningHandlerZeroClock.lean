import SteppedFlapjack.WordToStackSteps.ReturningZeroClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler

/-! Zero-extra-clock execution for returning calls with handlers. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs.CallReturnHandler

/-- The original handler induction hypotheses follow from proved loop blocks. -/
theorem handlerOriginalIH_of_blocks {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (handlerVar h1 h2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (retBlock : LoopBlock retCode) (handlerBlock : LoopBlock handlerCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p) :
    InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source := by
  refine ⟨?_, ?_, ?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact zeroSimulation_original ac retCode _ (loopBlock_zero ac retCode _ retBlock)
  · intro xs args1 prog ss envs location value calleePost facts
    exact zeroSimulation_original ac handlerCode _ (loopBlock_zero ac handlerCode _ handlerBlock)
  · intro xs args1 prog ss envs facts
    have find := facts.1.2.2.1
    obtain ⟨loc, lookup, _, _, _⟩ := CallTail.findCode_facts dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) source.code source.stackSize args1 prog ss find
    exact zeroSimulation_original ac prog _ (loopBlock_zero ac prog _ (code loc args1.length prog lookup))

/-- A normal handler-call continuation executes at the existing target clock. -/
theorem zeroHandlerNormalContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (retBlock : LoopBlock retCode) (handlerBlock : LoopBlock handlerCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate
        (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled),
          target) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have ih := handlerOriginalIH_of_blocks ac values names retCode handlerCode l1 l2 dest args handlerVar h1 h2 source retBlock handlerBlock code
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,continuationIH⟩ := sourceHandlerReturningContinuation
      ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
      result xs args1 prog ss envs location returnedValues guards ih nonzero wholeRun notError bodyRun
  have lengthEq : returnedValues.length = values.length := by omega
  obtain ⟨restoredSource,restored,restoredPop,restoreRun,restoredRelation⟩ :=
    restoreHandlerCallerFromBodyReturn ac k frame payload source bodyPost originalTarget target lens prior
      values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs guards
      conventions maximum location returnedValues lengthEq bodyRun calleeSize calleeFrame bodyConclusion
  have sourceSame : restoredSource = popped := Option.some.inj (restoredPop.symm.trans popRun)
  rw [sourceSame] at restoredRelation
  have mono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) .skip)) target restored none restoreRun
  have restoredBitmapBound : n-(appListAppend bs).length ≤ restored.bitmaps.length :=
    bitmapBound.trans mono.1.length_le
  have restoredBitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n-(appListAppend bs).length)) := bitmapPrefix.trans (mono.1.drop _)
  have restoredLabels : ∀ loc, StackSem.getLabelsExact compiled loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset target.code restored.code mono.2 loc (labels loc member)
  have retConventions := (CallReturning.returningConventions k values names retCode l1 l2 dest args
    (conventionsWithoutHandler k values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) conventions)).1
  have retFlat : flatExpConventions retCode = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact flat.1
  have retMax : maxVarHOL retCode < 2*payload+2*k := by
    simp only [maxVarHOL,Flapjack.WordAlloc.max3Eq] at maximum
    omega
  obtain ⟨targetPost,targetResult,continuationRun,conclusion⟩ :=
    loopBlock_zero ac retCode _ retBlock k frame payload sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceContinuation,notError,restoredRelation,retConventions,retFlat,compilation,
        lengthBound,restoredBitmapBound,restoredBitmapPrefix,restoredLabels,retMax⟩
  have sourceHandler : (WordSemStateFiniteExact.setVars values returnedValues popped).handler =
      source.handler := by rw [poppedEq]; rfl
  refine ⟨targetPost,targetResult,?_,?_⟩
  · rw [handlerRestoreContinuationSequence,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,restoreRun]
    exact continuationRun
  · unfold compCorrectResult at conclusion ⊢
    rw [sourceHandler] at conclusion
    exact conclusion


/-- An exception handler continuation executes at the existing target clock. -/
theorem zeroHandlerExceptionContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (retBlock : LoopBlock retCode) (handlerBlock : LoopBlock handlerCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false handlerCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate
        (compiled,
          target) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have ih := handlerOriginalIH_of_blocks ac values names retCode handlerCode l1 l2 dest args handlerVar h1 h2 source retBlock handlerBlock code
  obtain ⟨valid,domain,sourceContinuation,continuationIH⟩ := sourceHandlerExceptionContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location value guards ih nonzero wholeRun notError bodyRun
  obtain ⟨restoredRelation,handlerEq⟩ := restoreHandlerCallerFromBodyException ac k frame payload
    source sourcePost bodyPost originalTarget target lens prior values names retCode handlerCode
    l1 l2 h1 h2 handlerVar dest args conventions maximum xs args1 prog ss envs guards ih nonzero
    result wholeRun notError location value bodyRun calleeSize calleeFrame bodyConclusion
  have handlerConventions : postAllocConventionsHOL k handlerCode = true := by
    simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,Bool.and_eq_true] at conventions ⊢
    aesop (config := { enableSimp := false })
  have handlerFlat : flatExpConventions handlerCode = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact flat.2
  have handlerMax : maxVarHOL handlerCode < 2*payload+2*k := by
    simp only [maxVarHOL,Flapjack.WordAlloc.max3Eq] at maximum
    omega
  obtain ⟨targetPost,targetResult,continuationRun,conclusion⟩ :=
    loopBlock_zero ac handlerCode _ handlerBlock k frame payload sourcePost target result bs bsPost n nPost compiled lens
      ⟨sourceContinuation,notError,restoredRelation,handlerConventions,handlerFlat,compilation,
        lengthBound,bitmapBound,bitmapPrefix,labels,handlerMax⟩
  refine ⟨targetPost,targetResult,continuationRun,?_⟩
  unfold compCorrectResult at conclusion ⊢
  change bodyPost.handler = source.handler at handlerEq
  simp only [WordSemStateFiniteExact.setVar,handlerEq] at conclusion
  exact conclusion


/-- Enter and execute the callee without adding target clock. -/
theorem zeroHandlerCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
    (space : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3)
    (nonzero : source.clock ≠ 0)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) = (bodyResult,bodyPost))
    (bodyBlock : LoopBlock prog) :
    ∃ (destinationTarget saved header moved entry targetPost : StackSemStateFiniteExact width C F)
      (calleeCode body : HolProg width) (calleeSize calleeFrame : Nat)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (destinationCode,target) = (none,destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode,destinationTarget) = (none,saved) ∧
      StackSemEvaluate.evaluate (pushHandlerNative false h1 h2 (k,f,frame),saved) = (none,header) ∧
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination (args.length+1) (k,f,frame),header) =
          (none,moved) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode ∧
      calleeCode = .seq (.stackAlloc (calleeSize-(args1.length-k))) body ∧
      StackSemEvaluate.evaluate (.stackAlloc (calleeSize-(args1.length-k)),
        StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none,entry) ∧
      StackSemEvaluate.evaluate (body,entry) =
        (targetResult,targetPost) ∧
      StackSemEvaluate.evaluate
        (calleeCode,StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))) bodyPost targetPost bodyResult
        targetResult (frame :: lens) := by
  let expectedFrame := max (maxVarHOL prog / 2 + 1-k) (args1.length-k)
  have countEq := CallReturning.stackArgumentCount values names retCode l1 l2 dest args
    source xs args1 prog ss envs k f frame destinationCode destination guards destinationCompile
  have countBound : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
      target.stackSpace-3 := by
    rw [countEq]
    have capacity : args1.length-k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at space <;> omega
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleeBsPost,
    calleeIndex,calleeIndexPost,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,calleeBitmapLength,
    calleeBitmapBound,calleeBitmapPrefix,calleeLocalsSize,found,savedLookup,headerState,
    savedSpace,_,_⟩ := prepareHandlerCalleeDestination ac k f frame values names retCode l1 l2
      dest args handlerVar h1 h2 handlerCode source target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions
      maximum destinationCompile savedCompile bitmapLength bitmapBound bitmapPrefix room
      location countBound
  obtain ⟨body,calleeFrame,codeEq,bodyCompile,shape,argumentBound,bodyMaximum,frameEq⟩ :=
    calleeBodyCompilation ac k args1.length prog calleeBs calleeBsPost calleeIndex
      calleeIndexPost calleeCode calleeSize calleeCompile
  have frameSpace : calleeSize ≤ (pushedHandlerState saved h1 h2 k savedHandler).stackSpace := by
    change calleeSize ≤ saved.stackSpace-3
    rw [savedSpace]
    change calleeFrame = expectedFrame at frameEq
    rw [frameEq] at shape
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at shape space <;> omega
  obtain ⟨movedAgain,entry,moveAgain,allocateRun,entryRelation⟩ := enterHandlerCallee ac k f frame
    calleeSize calleeFrame values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
    savedHandler source saved lens xs args1 prog ss envs destinationCode destination guards
    savedRelation prePushRelation conventions maximum destinationCompile savedLookup
    (by rw [savedSpace]; exact room) shape calleeLocalsSize argumentBound frameSpace
  rw [← headerState] at moveAgain
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  have destinationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun
  have savedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun
  have headerMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (pushHandlerNative false h1 h2 (k,f,frame)) saved header none pushRun
  have movedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)) header moved none moveRun
  have allocationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize-(args1.length-k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) entry none allocateRun
  have allocationBitmaps : moved.bitmaps.IsPrefix entry.bitmaps := allocationMono.1
  have allocationCode : sptSubspt moved.code entry.code := allocationMono.2
  have bitmapGrowth := destinationMono.1.trans (savedMono.1.trans
    (headerMono.1.trans (movedMono.1.trans allocationBitmaps)))
  have entryBitmapBound := calleeBitmapBound.trans bitmapGrowth.length_le
  have entryBitmapPrefix := calleeBitmapPrefix.trans
    (bitmapGrowth.drop (calleeIndex-(appListAppend calleeBs).length))
  have bodyLabels : ∀ label, StackSem.getLabelsExact body label →
      StackSem.locCheckExact entry.code label := by
    intro label member
    apply LocationLabels.locCheckSubset moved.code entry.code allocationCode label
    apply StackPropsCodeLabels.findCodeImpGetLabels destination (moved.regs.eraseEq 0)
      moved.code calleeCode found label
    rw [codeEq,StackSem.getLabelsExact]
    exact Or.inr member
  obtain ⟨_,_,_,_,_,_,_,_,_,_,bodyConventions,bodyFlat,_⟩ :=
    CallReturning.calleeCompilation ac k f frame values names retCode l1 l2 dest args
      source target lens xs args1 prog ss envs guards related
  have bodyNotError := handlerCalleeNotError values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) source sourcePost bodyPost result bodyResult
    xs args1 prog ss envs guards nonzero wholeExecution notError bodyRun
  obtain ⟨targetPost,targetResult,execution,conclusion⟩ :=
    loopBlock_zero ac prog _ bodyBlock k calleeSize calleeFrame bodyPost entry bodyResult calleeBs calleeBsPost
      calleeIndex calleeIndexPost body (frame :: lens)
      ⟨bodyRun,bodyNotError,entryRelation,bodyConventions,bodyFlat,bodyCompile,
        calleeBitmapLength,entryBitmapBound,entryBitmapPrefix,bodyLabels,bodyMaximum⟩
  have calleeExecution : StackSemEvaluate.evaluate
      (calleeCode,StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
      (targetResult,targetPost) := by
    rw [codeEq,StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      allocateRun]
    exact execution
  exact ⟨destinationTarget,saved,header,moved,entry,targetPost,calleeCode,body,calleeSize,
    calleeFrame,targetResult,destinationRun,savedRun,pushRun,moveRun,found,codeEq,
    allocateRun,execution,calleeExecution,conclusion⟩


end SteppedFlapjack.WordToStackSteps
