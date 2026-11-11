import SteppedFlapjack.WordToStackSteps.ReturningZeroClock

/-! Assemble successful no-handler returning calls at zero extra clock. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

theorem zeroSuccessfulReturningCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (retZero : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t) → ZeroSimulation ac retCode t)
    (codeZero : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t) → ZeroSimulation ac p t)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace) :
    ∃ (targetFinal : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, target) =
        (targetResult, targetFinal) ∧
      compCorrectResult ac k f frame source sourcePost targetFinal result targetResult lens := by
  have ih := returningOriginalIH ac values names retCode l1 l2 dest args source
  let expectedFrame := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace := by
    rw [countEq]
    have bound : args1.length - k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    split_ifs at space <;> omega
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex) (k, f, frame)
    returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, argumentsRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, simulation⟩ :=
    simulatePreparedCalleeBody ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      savedPrefix sourcePost bodyPost result bodyResult ih nonzero execution notError bodyRun argumentsSpace
  have calleeSpace : calleeSize ≤ target.stackSpace := by
    change calleeFrame = expectedFrame at calleeFrameEq
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    rw [calleeFrameEq] at calleeShape
    split_ifs at calleeShape space <;> omega
  have destinationGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun).1
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun).1
  have bitmapGrowth : target.bitmaps.IsPrefix saved.bitmaps := destinationGrowth.trans savedGrowth
  have calleeSmaller : (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))).clock < source.clock := by
    simp only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv_clock,WordSemStateFiniteExact.decClock]
    omega
  have calleeSafe : safeWordCode source → safeWordCode (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) := by
    intro safe
    simpa [safeWordCode,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.code_pushEnv,
      WordSemStateFiniteExact.decClock] using safe
  obtain ⟨movedAgain, entry, calleeTarget, targetResult, moveAgain, allocationRun, bodyTargetRun,
    calleeRun0, bodyConclusion⟩ :=
    zeroCalleeBodyAt ac k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile (codeZero location args1.length prog sourceCode _ calleeSmaller calleeSafe)
      nonzero execution notError bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans argumentsRun)
  subst movedAgain
  let bodyExtra := 0
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + bodyExtra}) = (targetResult, calleeTarget) := by
    simpa [bodyExtra, StackSemStateOps.setVar] using calleeRun0
  have savedPrelude : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, saved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    exact savedRun
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, f, frame))), target) = (none, moved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact argumentsRun
  have free := completePreludeClockFree (C := C) (F := F) k f frame dest args names
    (bs, n) (savedBitmaps, savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode
      (stackArgsNative destination (args.length + 1) (k, f, frame))), target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode
          (stackArgsNative destination (args.length + 1) (k, f, frame))), target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq, ← related.1]; exact nonzero
  let callee : HolProg width := .seq (.stackAlloc (calleeSize - (args1.length - k))) body
  let continuation : HolProg width := .seq .skip (copyRetNative false false (k, f, frame) values returnCode)
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled, target) =
          (finalResult, targetFinal) ∧
        compCorrectResult ac k f frame source sourcePost targetFinal result finalResult lens := by
    obtain ⟨callRun, conclusion⟩ := terminalCallFromCallee ac k f frame calleeSize calleeFrame values
      names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult target moved calleeTarget
      targetResult lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
      nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    refine ⟨calleeTarget, targetResult, ?_, conclusion⟩
    simpa [bodyExtra] using completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
        finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
        target moved calleeTarget bodyExtra targetResult destinationCompile savedCompile returnCompile
        compilation preludeRun callRun
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun notError
    rcases outcomes with ⟨returnLocation, returned, rfl⟩ | ⟨exceptionLocation, value, rfl⟩ |
      timeout | resource | ⟨event, ffi⟩
    · have targetEq : targetResult = some (.result returnLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      exact zeroCompiledNormalFromHistory ac k f frame calleeSize calleeFrame values names retCode
        l1 l2 dest args source sourcePost bodyPost result returnLocation returned saved calleeTarget lens
        xs args1 prog ss envs guards savedRelation conventions maximum retZero nonzero execution notError
        bodyRun bodyConclusion target moved bs savedBitmaps finalBitmaps n savedIndex finalIndex
        destinationCode savedCode returnCode compiled callee destination flat destinationCompile
        savedCompile returnCompile compilation bitmapLength bitmapBound bitmapPrefix labels savedPrelude
        argumentsRun calleeRun0 found
    · have targetEq : targetResult = some (.exception exceptionLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨callRun, conclusion⟩ := exceptionCallFromCallee ac k f frame calleeSize calleeFrame values
        names retCode l1 l2 dest args source sourcePost bodyPost result exceptionLocation value target moved
        calleeTarget lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
        nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion
      refine ⟨calleeTarget, some (.exception exceptionLocation), ?_, conclusion⟩
      simpa [bodyExtra] using completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
          finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
          target moved calleeTarget bodyExtra (some (.exception exceptionLocation)) destinationCompile
          savedCompile returnCompile compilation preludeRun callRun
    · apply finishTerminal; left
      simpa only [timeout, Option.map_some, compileResult] using matching.symm
    · apply finishTerminal; right; left
      exact ⟨.word 1, by simpa only [resource, Option.map_some, compileResult] using matching.symm⟩
    · apply finishTerminal; right; right
      exact ⟨event, by simpa only [ffi, Option.map_some, compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2, mismatch.1⟩))

theorem zeroReturningNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (retZero : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t) → ZeroSimulation ac retCode t)
    (codeZero : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t) → ZeroSimulation ac p t) :
    ZeroSimulation ac (.call (some (values, names, retCode, l1, l2)) dest args none) source := by
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, bitmapLength,
    bitmapBound, bitmapPrefix, labels, maximum⟩ := premises
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotError values names retCode l1 l2
    dest args source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k, f, frame) with ⟨destinationCode, destination⟩
  rcases savedCompile : wLiveNative names (bs, n) (k, f, frame) with
    ⟨savedCode, savedBitmaps, savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) with
    ⟨returnCode, returnBitmaps, returnIndex⟩
  have shape := compilation
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at shape
  obtain ⟨bitmapsEq, indexEq⟩ := shape.2
  subst finalBitmaps
  subst finalIndex
  by_cases argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace
  · by_cases zero : source.clock = 0
    · obtain ⟨targetPost, run, conclusion⟩ := compiledCallTimeout ac k f frame values names retCode
        l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
        returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
        related conventions maximum destinationCompile savedCompile returnCompile bitmapLength
        bitmapBound compiled compilation execution argumentsSpace zero bitmapPrefix
      exact ⟨targetPost, some .timeOut, run, conclusion⟩
    · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
          else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace
      · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
          ⟨bodyResult, bodyPost⟩
        exact zeroSuccessfulReturningCall ac k f frame values names retCode l1 l2 dest args source target
          lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex
          destinationCode savedCode returnCode compiled destination guards related conventions maximum
          destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound
          bitmapPrefix sourcePost bodyPost result bodyResult retZero codeZero zero execution notError bodyRun calleeSpace
      · obtain ⟨calleeSize, _, sizeEq, failure⟩ := compiledCalleeFrameFailure ac k f frame values names
          retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
          returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
          related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound
          compiled compilation execution argumentsSpace zero bitmapPrefix
        obtain ⟨targetPost, run, conclusion⟩ := failure (by rw [sizeEq]; omega)
        exact ⟨targetPost, some (.halt (.word (BitVec.ofNat width 2))), run, conclusion⟩
  · obtain ⟨targetPost, run, conclusion⟩ := compiledStackArgumentsFailure ac k f frame values names
      retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
      returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related
      conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled
      compilation execution (by omega) bitmapPrefix
    exact ⟨targetPost, some (.halt (.word (BitVec.ofNat width 2))), run, conclusion⟩


/-- A matching normal returning call without a handler has an actual compiled
run related to the source outcome and bounded by a computable target cost
at the source-step limit. -/
theorem normalReturningNone_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (source middle restored post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (xs values ys : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs bsPost : AppList (BitVec width)) (n nPost k f frame limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (code : ∀ loc arity prog, sptLookup loc source.code = some (arity, prog) → LoopBlock prog)
    (retBlock : LoopBlock continuation)
    (hargs : WordSemStateFiniteExact.getVars args source = some xs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      source.code source.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts source.locals = some envs) (hclock : source.clock ≠ 0)
    (bodyRun : WordSemStateFiniteExact.evaluate callee
      (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result (.loc l1 l2) ys), middle)) (hlen : ys.length = names.length)
    (pop : WordSemStateFiniteExact.popEnv middle = some restored)
    (hdom : sptDomainEqUnion restored.locals envs.1 envs.2)
    (notTimeout : result ≠ some .timeOut)
    (stepBound : WordSteps.steps (.call (some (names, cuts, continuation, l1, l2)) dest args none) source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args none) source = (result, post) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.call (some (names, cuts, continuation, l1, l2)) dest args none) = true ∧
      flatExpConventions (.call (some (names, cuts, continuation, l1, l2)) dest args none) = true ∧
      compNative ac false (.call (some (names, cuts, continuation, l1, l2)) dest args none) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.call (some (names, cuts, continuation, l1, l2)) dest args none) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {post with clock := limit - (source.clock - post.clock)} targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := limit}) ≤ returningChainCost limit target.code compiled := by
  have ⟨normalized, bound⟩ := normalReturn_normalized_target_bound ac dest args names cuts continuation l1 l2 none
    source middle restored post target result xs values ys ss callee envs (bs, n) k f frame limit lens
    premises.2.2.1 code retBlock (by simp) hargs hbad hfind hvalid hcut hclock bodyRun hlen pop hdom
    premises.1 notTimeout stepBound
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity p, sptLookup loc ({source with clock := limit}).code = some (arity, p) → LoopBlock p := code
  have sim := zeroReturningNone ac names cuts continuation l1 l2 dest args {source with clock := limit}
    (fun t _ _ => loopBlock_zero ac continuation t retBlock)
    (fun loc arity p lookup t _ _ => loopBlock_zero ac p t (normalizedCode loc arity p lookup))
  obtain ⟨targetPost, targetResult, targetRun, conclusion⟩ := sim k f frame
    {post with clock := limit - (source.clock - post.clock)} {target with clock := limit} result
    bs bsPost n nPost compiled lens ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  rw [premises.2.2.2.2.2.1] at bound
  exact ⟨targetPost, targetResult, targetRun, conclusion, bound⟩

end SteppedFlapjack.WordToStackSteps
