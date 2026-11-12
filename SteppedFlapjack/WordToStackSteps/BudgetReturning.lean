import SteppedFlapjack.WordToStackSteps.ReturningZeroClock
import SteppedFlapjack.WordToStackSteps.ReturningNoneSteps
import SteppedFlapjack.WordToStackSteps.BudgetSimulation
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- If the overall returning call finishes without timing out, its reached
callee also finishes without timing out. -/
theorem calleeNotTimeout {width : Nat} [NeZero width] {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source sourcePost calleePost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args handler) source =
      (result, sourcePost)) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, calleePost)) : bodyResult ≠ some .timeOut := by
  intro timeout
  rw [timeout] at bodyRun
  obtain ⟨get, bad, find, valid, cut⟩ := guards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only [Prod.mk.injEq] at execution
  exact absurd execution.1.symm notTimeout


/-- Enter a callee while preserving clock credit for its caller. -/
theorem rateCalleeBodyAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (rate cost reserve : Nat)
    (bodyBudget : RateSimulation ac rate cost prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))))
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + rate*(source.clock-1) + cost + reserve}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + rate*(source.clock-1) + cost + reserve}) =
            (targetResult, targetPost) ∧
          reserve ≤ targetPost.clock ∧
          (targetResult = some (.halt (.word 2)) ∨
        ((rate+1)*bodyPost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ bodyPost.clock + rate*(source.clock-1) + cost + reserve)) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost {targetPost with clock := bodyPost.clock} bodyResult targetResult (callerFrame :: lens) := by
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  have bodyNotTimeout := calleeNotTimeout values names retCode l1 l2 dest args none source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notTimeout bodyRun
  obtain ⟨targetPost, targetResult, targetRun, enough, accounting, conclusion⟩ :=
    bodyBudget k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, bodyNotTimeout, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩ reserve
  simp only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv_clock,WordSemStateFiniteExact.decClock] at targetRun accounting
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + rate*(source.clock-1) + cost + reserve}) =
      (targetResult, targetPost) := by
    have boosted := Compiler.Backend.StackProps.evaluateAddClock (rate*(source.clock-1) + cost + reserve)
      (.stackAlloc (calleeSize - (args1.length-k)))
      (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
      none entry ⟨allocationRun, by simp⟩
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
    simp only [Nat.add_assoc, StackSemStateOps.setVar] at boosted ⊢
    rw [boosted]
    simpa only [Nat.add_assoc] using targetRun
  exact ⟨moved, entry, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, enough, accounting, conclusion⟩




theorem budgetCalleeBodyAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (cost reserve : Nat)
    (bodyBudget : BudgetSimulation ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) cost)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + cost + reserve}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + cost + reserve}) =
            (targetResult, targetPost) ∧
          reserve ≤ targetPost.clock ∧
          (targetResult = some (.halt (.word 2)) ∨
        (bodyPost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ bodyPost.clock + cost + reserve)) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost {targetPost with clock := bodyPost.clock} bodyResult targetResult (callerFrame :: lens) := by
  have sim := budget_to_rate ac 0 cost prog _ bodyBudget
  simpa using rateCalleeBodyAt ac k callerSize callerFrame values names retCode l1 l2 dest args
    source sourcePost bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
    guards callerRelation pushedRelation conventions maximum destinationCompile 0 cost reserve sim nonzero
    execution notError notTimeout bodyRun location calleeSize calleeFrame body bs bsPost n nPost
    targetCode bodyCompile bodyConventions bodyFlat bitmapLength bitmapBound bitmapPrefix calleeLocalsSize
    calleeShape argumentBound bodyMaximum space


/-- Restore a continuation while preserving remaining clock credit. -/
theorem rateReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F) (rate cost : Nat)
    (retBudget : RateSimulation ac rate cost retCode source)
    (target restored : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width) (lens : List Nat)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true) (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored))
    (reserve : Nat) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values compiled,
        {target with clock := target.clock + rate*source.clock + cost + reserve}) = (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        ((rate+1)*sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + rate*source.clock + cost + reserve)) ∧
      compCorrectResult ac k f frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  obtain ⟨post, out, continuationRun, enough, accounting, conclusion⟩ :=
    retBudget k f frame sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceRun, notError, notTimeout, related, conventions, flat, compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maximum⟩ reserve
  have boosted := Compiler.Backend.StackProps.evaluateAddClock (rate*source.clock + cost + reserve)
    (copyRetNative false false (k,f,frame) values .skip) target none restored ⟨copyRun, by simp⟩
  refine ⟨post, out, ?_, enough, accounting, conclusion⟩
  rw [CallReturnEval.evaluateCopyRetSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate]
  simp only [Nat.add_assoc] at boosted ⊢
  rw [boosted]
  simpa only [Nat.add_assoc] using continuationRun

theorem budgetReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F) (cost : Nat)
    (retBudget : BudgetSimulation ac retCode source cost)
    (target restored : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width) (lens : List Nat)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true) (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored))
    (reserve : Nat) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (copyRetNative false false (k, f, frame) values compiled,
        {target with clock := target.clock + cost + reserve}) = (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + cost + reserve)) ∧
      compCorrectResult ac k f frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  have sim := budget_to_rate ac 0 cost retCode source retBudget
  simpa using rateReturningContinuation ac k f frame values retCode source sourcePost 0 cost sim
    target restored result bs bsPost n nPost compiled lens sourceRun notError notTimeout related conventions
    flat compilation lengthBound bitmapBound bitmapPrefix labels maximum copyRun reserve


/-- Restore the ordinary caller and pass the callee’s remaining clock to its continuation. -/
theorem rateContinuationFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (rate cost reserve : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate cost retCode t)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {target with clock := bodyPost.clock} (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (enough : bodyPost.clock + rate*bodyPost.clock + cost + reserve ≤ target.clock)
    (bounded : target.clock ≤ bodyPost.clock + bodyExtraClock)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, {target with clock := bodyPost.clock}) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          target) = (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        ((rate+1)*sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + bodyExtraClock)) ∧
      compCorrectResult ac k callerSize frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  have ih := returningOriginalIH ac values names retCode l1 l2 dest args source
  obtain ⟨popped, restored, popRun, sourceContinuation, _, copyRun, restoredRelation⟩ :=
    restoreCallerFromBodyReturn ac k callerSize frame calleeSize calleeFrame values names
      retCode l1 l2 dest args source sourcePost bodyPost result location returned saved {target with clock := bodyPost.clock}
      lens xs args1 prog ss envs guards callerRelation conventions maximum ih nonzero
      execution notError bodyRun bodyConclusion
  obtain ⟨retConventions, retFlat, retMaximum, retLength, retBitmapBound, retBitmapPrefix, retLabels⟩ :=
    continuationCompilationFacts ac k callerSize frame values names retCode l1 l2 dest args
      initial bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode compiled destination conventions flat maximum destinationCompile savedCompile
      returnCompile compilation lengthBound bitmapBound bitmapPrefix labels
  let slack := target.clock - bodyPost.clock
  have clockEq : bodyPost.clock + slack = target.clock := by dsimp [slack]; omega
  have copyBoosted := Compiler.Backend.StackProps.evaluateAddClock slack
    (copyRetNative false false (k,callerSize,frame) values .skip)
    {target with clock := bodyPost.clock} none restored ⟨copyRun,by simp⟩
  have copyActual : StackSemEvaluate.evaluate
      (copyRetNative false false (k,callerSize,frame) values .skip,target) =
      (none,{restored with clock := restored.clock + slack}) := by
    simpa only [clockEq] using copyBoosted
  have growth := returningHistoryGrowth initial saved moved target {restored with clock := restored.clock + slack}
    (.seq destinationCode savedCode)
    (stackArgsNative destination (args.length + 1) (k, callerSize, frame)) callee
    k callerSize frame l1 l2 bodyExtraClock values (some (.result location))
    preludeRun argumentsRun calleeRun copyActual
  have bitmapGrowth : initial.bitmaps.IsPrefix restored.bitmaps := growth.1
  have codeGrowth : sptSubspt initial.code restored.code := growth.2
  have restoredLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset initial.code restored.code codeGrowth loc (retLabels loc member)
  have bodyClock := (WordSemStateFiniteExact.evaluate_clock prog _ _ _ bodyRun).1
  simp only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv_clock,
    WordSemStateFiniteExact.decClock] at bodyClock
  have poppedClock := WordSemStateFiniteExact.popEnv_clock bodyPost popped popRun
  have contClock : (WordSemStateFiniteExact.setVars values returned popped).clock = bodyPost.clock := by
    simpa only [WordSemStateFiniteExact.setVars] using poppedClock
  have smaller : (WordSemStateFiniteExact.setVars values returned popped).clock < source.clock := by
    simp only [WordSemStateFiniteExact.setVars]
    omega
  have safeTransfer : safeWordCode source → safeWordCode (WordSemStateFiniteExact.setVars values returned popped) ∧
      (WordSemStateFiniteExact.setVars values returned popped).code = source.code := by
    intro safe
    have postSafe := handlerCallee_safe source bodyPost (some (values,names,retCode,l1,l2)) dest xs args1 prog ss envs
      none _ guards.2.2.1 bodyRun safe
    have postCode := handlerCallee_code source bodyPost (some (values,names,retCode,l1,l2)) dest xs args1 prog ss envs
      none _ guards.2.2.1 bodyRun safe
    have h := WordSemStateFiniteExact.popEnvConst bodyPost popped popRun
    have codeEq : popped.code = bodyPost.code := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    constructor
    · simpa [safeWordCode,WordSemStateFiniteExact.setVars,codeEq] using postSafe
    · simpa [WordSemStateFiniteExact.setVars,codeEq] using postCode
  let remaining := slack - rate*bodyPost.clock - cost
  have remainingLower : reserve ≤ remaining := by dsimp [remaining,slack]; omega
  have remainingUpper : rate*bodyPost.clock + cost + remaining ≤ bodyExtraClock := by dsimp [remaining,slack]; omega
  have remainingEq : bodyPost.clock + rate*bodyPost.clock + cost + remaining = target.clock := by dsimp [remaining,slack]; omega
  obtain ⟨targetPost, targetResult, targetContinuation, postEnough, accounting, conclusion⟩ :=
    rateReturningContinuation ac k callerSize frame values retCode
      (WordSemStateFiniteExact.setVars values returned popped) sourcePost
      rate cost (retBudget _ smaller safeTransfer) {target with clock := bodyPost.clock} restored result
      savedBitmaps finalBitmaps savedIndex finalIndex returnCode lens
      sourceContinuation notError notTimeout restoredRelation retConventions retFlat returnCompile retLength
      (retBitmapBound.trans bitmapGrowth.length_le)
      (retBitmapPrefix.trans (bitmapGrowth.drop _)) restoredLabels retMaximum copyRun remaining
  rw [contClock] at targetContinuation accounting
  obtain ⟨gc, tail, sourceFrame, _, _, sourceHandler, _, _⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  have poppedHandler : popped.handler = bodyPost.handler := by
    have pop := popRun
    rw [WordSemStateFiniteExact.popEnv, sourceFrame] at pop
    have shape := Option.some.inj pop
    rw [← shape]
  have handler : (WordSemStateFiniteExact.setVars values returned popped).handler = source.handler :=
    poppedHandler.trans sourceHandler
  rw [returningResultInitialHandler ac k callerSize frame source
    (WordSemStateFiniteExact.setVars values returned popped) sourcePost {targetPost with clock := sourcePost.clock}
    result targetResult lens handler] at conclusion
  refine ⟨popped, restored, targetPost, targetResult, popRun, copyRun, ?_, by omega, ?_, conclusion⟩
  · simpa only [remainingEq] using targetContinuation
  · rcases accounting with limit | ⟨lower,upper⟩
    · exact Or.inl limit
    · right; constructor <;> omega




theorem budgetContinuationFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (cost reserve : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac retCode t cost)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {target with clock := bodyPost.clock} (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (enough : bodyPost.clock + cost + reserve ≤ target.clock)
    (bounded : target.clock ≤ bodyPost.clock + bodyExtraClock)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, {target with clock := bodyPost.clock}) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          target) = (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + bodyExtraClock)) ∧
      compCorrectResult ac k callerSize frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  have retRate : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 cost retCode t := by
    intro t smaller transfer
    exact budget_to_rate ac 0 cost retCode t (retBudget t smaller transfer)
  simpa using rateContinuationFromHistory ac k callerSize frame calleeSize calleeFrame values names retCode l1 l2 dest args
    source sourcePost bodyPost result location returned saved target lens xs args1 prog ss envs guards callerRelation
    conventions maximum 0 cost reserve retRate nonzero execution notError notTimeout bodyRun bodyConclusion initial moved
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock (by simpa using enough) bounded flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun


/-- Compose the compiled ordinary caller with its reserved continuation. -/
theorem rateContinuationCompiledFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (rate cost reserve : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate cost retCode t)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {target with clock := bodyPost.clock} (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (enough : bodyPost.clock + rate*bodyPost.clock + cost + reserve ≤ target.clock)
    (bounded : target.clock ≤ bodyPost.clock + bodyExtraClock)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some callee) :
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {initial with clock := initial.clock + bodyExtraClock}) =
        (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        ((rate+1)*sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + bodyExtraClock)) ∧
      compCorrectResult ac k callerSize frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  have ih := returningOriginalIH ac values names retCode l1 l2 dest args source
  obtain ⟨_, _, _, _, _, _, _, _, _, _, valid, _, _⟩ := sourceReturningContinuation ac values names
    retCode l1 l2 dest args source sourcePost bodyPost result xs args1 prog ss envs location
    returned guards ih nonzero execution notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨popped, restored, finalTarget, finalResult, _, _, continuationRun,
    postEnough, accounting, conclusion⟩ := rateContinuationFromHistory ac k callerSize frame calleeSize
    calleeFrame values names retCode l1 l2 dest args source sourcePost bodyPost result location
    returned saved target lens xs args1 prog ss envs guards callerRelation conventions maximum
    rate cost reserve retBudget nonzero execution notError notTimeout bodyRun bodyConclusion initial moved bs savedBitmaps finalBitmaps
    n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock enough bounded flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun
  have argumentClock := stackArgumentsClockFree (C := C) (F := F) k callerSize frame
    destination (args.length + 1) saved saved.clock
  change StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) =
    Prod.map id (fun state => {state with clock := saved.clock})
      (StackSemEvaluate.evaluate
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved)) at argumentClock
  rw [argumentsRun] at argumentClock
  have movedClock : moved.clock = saved.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj argumentClock).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedClock, ← callerRelation.1]
    exact nonzero
  have actualContinuation : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode),
        target) = (finalResult, finalTarget) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    exact continuationRun
  rw [locationEq] at calleeRun
  have callRun := returningCallContinuationRun moved target finalTarget l1 l2 bodyExtraClock
    0 destination callee
    (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode)) finalResult
    found movedNonzero calleeRun (by simpa using actualContinuation)
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame))), initial) =
      (none, moved) := by
    rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, preludeRun]
    exact argumentsRun
  refine ⟨finalTarget, finalResult, ?_, postEnough, accounting, conclusion⟩
  exact completeCallFromPrelude ac k callerSize frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination initial moved finalTarget bodyExtraClock finalResult
    destinationCompile savedCompile returnCompile compilation completePrelude (by simpa using callRun)




theorem budgetContinuationCompiledFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (cost reserve : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac retCode t cost)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {target with clock := bodyPost.clock} (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (enough : bodyPost.clock + cost + reserve ≤ target.clock)
    (bounded : target.clock ≤ bodyPost.clock + bodyExtraClock)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some callee) :
    ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {initial with clock := initial.clock + bodyExtraClock}) =
        (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + bodyExtraClock)) ∧
      compCorrectResult ac k callerSize frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  have retRate : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 cost retCode t := by
    intro t smaller transfer
    exact budget_to_rate ac 0 cost retCode t (retBudget t smaller transfer)
  simpa using rateContinuationCompiledFromHistory ac k callerSize frame calleeSize calleeFrame values names retCode l1 l2 dest args
    source sourcePost bodyPost result location returned saved target lens xs args1 prog ss envs guards callerRelation
    conventions maximum 0 cost reserve retRate nonzero execution notError notTimeout bodyRun bodyConclusion initial moved
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock (by simpa using enough) bounded flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun found


/-- Terminal callee outcomes propagate through an ordinary call. -/
theorem budgetTerminalCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (initial moved targetPost : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width)) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (extra : Nat) (destination : Sum Nat Nat) (body continuation : HolProg width)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some body)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + extra}) = (targetResult, targetPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {targetPost with clock := bodyPost.clock} bodyResult targetResult (callerFrame :: lens))
    (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
      ∃ event, targetResult = some (.finalFFI event)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination none,
        {moved with clock := moved.clock + extra}) = (targetResult, targetPost) ∧
    compCorrectResult ac k callerSize callerFrame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens := by
  constructor
  · exact returningCallTerminalRun moved targetPost l1 l2 extra destination body continuation
      targetResult found movedNonzero calleeRun terminal
  · have normalized : compCorrectResult ac k callerSize callerFrame source sourcePost
        {targetPost with clock := bodyPost.clock} result targetResult lens := by
      by_cases matching : bodyResult.map compileResult = targetResult
      · exact bodyTerminalResult ac k callerSize callerFrame calleeSize calleeFrame values names
          retCode l1 l2 dest args source sourcePost bodyPost result bodyResult {targetPost with clock := bodyPost.clock} targetResult
          lens xs args1 prog ss envs guards nonzero execution bodyRun
          (matchingTerminalSource bodyResult targetResult matching terminal) bodyConclusion matching
      · exact bodyMismatchResult ac k callerSize callerFrame calleeSize calleeFrame values names
          retCode l1 l2 dest args source sourcePost bodyPost result bodyResult initial {targetPost with clock := bodyPost.clock}
          targetResult lens xs args1 prog ss envs guards callerRelation nonzero execution bodyRun
          bodyConclusion matching

    simpa using compCorrectResult_setClocks ac k callerSize callerFrame source sourcePost
      {targetPost with clock := bodyPost.clock} result targetResult lens sourcePost.clock normalized

/-- Unhandled exceptions propagate through an ordinary call. -/
theorem budgetExceptionCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (k callerSize callerFrame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width)) (location value : WordLocW width)
    (initial moved targetPost : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (extra : Nat) (destination : Sum Nat Nat) (body continuation : HolProg width)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source initial lens 0)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value), bodyPost))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some body)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (body, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + extra}) =
      (some (.exception location), targetPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost {targetPost with clock := bodyPost.clock} (some (.exception location value)) (some (.exception location))
      (callerFrame :: lens)) :
    StackSemEvaluate.evaluate
      (.call (some (continuation, 0, l1, l2)) destination none,
        {moved with clock := moved.clock + extra}) = (some (.exception location), targetPost) ∧
    compCorrectResult ac k callerSize callerFrame source sourcePost {targetPost with clock := sourcePost.clock} result
      (some (.exception location)) lens := by
  refine ⟨returningCallExceptionRun moved targetPost l1 l2 extra destination body continuation
      location found movedNonzero calleeRun, ?_⟩
  have normalized := bodyExceptionResult ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source sourcePost bodyPost result location value initial {targetPost with clock := bodyPost.clock} lens
      xs args1 prog ss envs guards callerRelation nonzero execution bodyRun bodyConclusion
  simpa using compCorrectResult_setClocks ac k callerSize callerFrame source sourcePost
      {targetPost with clock := bodyPost.clock} result (some (.exception location)) lens sourcePost.clock normalized



/-- A fitting ordinary call composes explicit callee and continuation budgets. -/
theorem rateSuccessfulReturningCall {width : Nat} [NeZero width] {C F : Type}
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
    (rate extra bodyCost contCost reserve : Nat)
    (bodyFits : bodyCost ≤ rate+extra)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate contCost retCode t)
    (codeBudget : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate bodyCost p t)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace) :
    ∃ (targetFinal : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + rate*source.clock + extra + contCost + reserve}) =
        (targetResult, targetFinal) ∧
      reserve ≤ targetFinal.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        ((rate+1)*sourcePost.clock + reserve ≤ targetFinal.clock ∧ targetFinal.clock ≤ sourcePost.clock + rate*source.clock + extra + contCost + reserve)) ∧
      compCorrectResult ac k f frame source sourcePost {targetFinal with clock := sourcePost.clock} result targetResult lens := by
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
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) ∧
      (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))).code = source.code := by
    intro safe
    constructor
    · simpa [safeWordCode,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.code_pushEnv,
        WordSemStateFiniteExact.decClock] using safe
    · simp [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.code_pushEnv,WordSemStateFiniteExact.decClock]
  obtain ⟨movedAgain, entry, calleeTarget, targetResult, moveAgain, allocationRun, bodyTargetRun,
    calleeRun0, calleeEnough, calleeAccounting, bodyConclusion⟩ :=
    rateCalleeBodyAt ac k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile rate bodyCost (rate+extra-bodyCost+contCost+reserve) (codeBudget location args1.length prog sourceCode _ calleeSmaller calleeSafe)
      nonzero execution notError notTimeout bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans argumentsRun)
  subst movedAgain
  let bodyExtra := rate*(source.clock-1) + bodyCost + (rate+extra-bodyCost+contCost+reserve)
  have creditEq : bodyExtra = rate*source.clock+extra+contCost+reserve := by
    have pred : source.clock-1+1 = source.clock := by omega
    have mul : rate*(source.clock-1)+rate = rate*source.clock := by
      calc
        _ = rate*(source.clock-1+1) := by simp [Nat.mul_add]
        _ = _ := by rw [pred]
    dsimp [bodyExtra]
    omega
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + bodyExtra}) = (targetResult, calleeTarget) := by
    simpa [bodyExtra, StackSemStateOps.setVar, Nat.add_assoc] using calleeRun0
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
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + rate*source.clock + extra + contCost + reserve}) =
          (finalResult, targetFinal) ∧
        reserve ≤ targetFinal.clock ∧
        (finalResult = some (.halt (.word 2)) ∨
          ((rate+1)*sourcePost.clock + reserve ≤ targetFinal.clock ∧ targetFinal.clock ≤ sourcePost.clock + rate*source.clock + extra + contCost + reserve)) ∧
        compCorrectResult ac k f frame source sourcePost {targetFinal with clock := sourcePost.clock} result finalResult lens := by
    obtain ⟨callRun, conclusion⟩ := budgetTerminalCallFromCallee ac k f frame calleeSize calleeFrame values
      names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult target moved calleeTarget
      targetResult lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
      nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    refine ⟨calleeTarget, targetResult, ?_, by omega, ?_, conclusion⟩
    · simpa [creditEq,Nat.add_assoc] using completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
        finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
        target moved calleeTarget bodyExtra targetResult destinationCompile savedCompile returnCompile
        compilation preludeRun callRun
    · by_cases matching : bodyResult.map compileResult = targetResult
      · have terminalSource := matchingTerminalSource bodyResult targetResult matching terminal
        obtain ⟨_, postEq⟩ := sourceCallTerminal values names retCode l1 l2 dest args source sourcePost
          bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun terminalSource
        rcases calleeAccounting with limit | ⟨lower,upper⟩
        · exact Or.inl limit
        · right; subst sourcePost; constructor <;> omega
      · unfold compCorrectResult at bodyConclusion
        rw [if_pos matching] at bodyConclusion
        exact Or.inl bodyConclusion.1
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun notError
    rcases outcomes with ⟨returnLocation, returned, rfl⟩ | ⟨exceptionLocation, value, rfl⟩ |
      timeout | resource | ⟨event, ffi⟩
    · have targetEq : targetResult = some (.result returnLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      have ⟨lower,upper⟩ := calleeAccounting.resolve_left (by simp [compileResult])
      simp only [Nat.add_mul,Nat.one_mul] at lower
      have assembled := rateContinuationCompiledFromHistory ac k f frame calleeSize calleeFrame values names retCode
        l1 l2 dest args source sourcePost bodyPost result returnLocation returned saved calleeTarget lens
        xs args1 prog ss envs guards savedRelation conventions maximum rate contCost reserve retBudget nonzero execution notError notTimeout
        bodyRun bodyConclusion target moved bs savedBitmaps finalBitmaps n savedIndex finalIndex
        destinationCode savedCode returnCode compiled callee destination bodyExtra (by omega) (by dsimp [bodyExtra]; omega) flat destinationCompile
        savedCompile returnCompile compilation bitmapLength bitmapBound bitmapPrefix labels savedPrelude
        argumentsRun calleeRun found
      simpa [creditEq,Nat.add_assoc] using assembled
    · have targetEq : targetResult = some (.exception exceptionLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨callRun, conclusion⟩ := budgetExceptionCallFromCallee ac k f frame calleeSize calleeFrame values
        names retCode l1 l2 dest args source sourcePost bodyPost result exceptionLocation value target moved
        calleeTarget lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
        nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion
      have ⟨_,postEq⟩ := sourceCallException values names retCode l1 l2 dest args source sourcePost bodyPost result
        exceptionLocation value xs args1 prog ss envs guards nonzero execution bodyRun
      have ⟨lower,upper⟩ := calleeAccounting.resolve_left (by simp [compileResult])
      refine ⟨calleeTarget, some (.exception exceptionLocation), ?_, by omega, ?_, conclusion⟩
      · simpa [creditEq,Nat.add_assoc] using completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
          finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
          target moved calleeTarget bodyExtra (some (.exception exceptionLocation)) destinationCompile
          savedCompile returnCompile compilation preludeRun callRun
      · right; subst sourcePost; constructor <;> omega
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




theorem budgetSuccessfulReturningCall {width : Nat} [NeZero width] {C F : Type}
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
    (bodyCost contCost reserve : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac retCode t contCost)
    (codeBudget : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac p t bodyCost)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace) :
    ∃ (targetFinal : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + bodyCost + contCost + reserve}) =
        (targetResult, targetFinal) ∧
      reserve ≤ targetFinal.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (sourcePost.clock + reserve ≤ targetFinal.clock ∧ targetFinal.clock ≤ sourcePost.clock + bodyCost + contCost + reserve)) ∧
      compCorrectResult ac k f frame source sourcePost {targetFinal with clock := sourcePost.clock} result targetResult lens := by
  have retRate : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 contCost retCode t := by
    intro t smaller transfer
    exact budget_to_rate ac 0 contCost retCode t (retBudget t smaller transfer)
  have codeRate : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 bodyCost p t := by
    intro loc arity p found t smaller transfer
    exact budget_to_rate ac 0 bodyCost p t (codeBudget loc arity p found t smaller transfer)
  simpa using rateSuccessfulReturningCall ac k f frame values names retCode l1 l2 dest args source target lens
    xs args1 prog ss envs bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
    guards related conventions maximum destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound bitmapPrefix
    sourcePost bodyPost result bodyResult 0 bodyCost bodyCost contCost reserve (by omega) retRate codeRate nonzero execution notError notTimeout bodyRun space


/-- Preserve arbitrary explicit reserve after a resource-limit halt. -/
theorem resourceWithReserve {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target targetPost : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width)) (compiled : HolProg width) (lens : List Nat)
    (cost reserve : Nat)
    (run : StackSemEvaluate.evaluate (compiled,target) = (some (.halt (.word 2)), targetPost))
    (relation : compCorrectResult ac k f frame source post targetPost result (some (.halt (.word 2))) lens) :
    ∃ final,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock + cost + reserve}) =
        (some (.halt (.word 2)),final) ∧ reserve ≤ final.clock ∧
      compCorrectResult ac k f frame source post {final with clock := post.clock} result (some (.halt (.word 2))) lens := by
  have boosted := Compiler.Backend.StackProps.evaluateAddClock (cost+reserve) compiled target
    (some (.halt (.word 2))) targetPost ⟨run,by simp⟩
  refine ⟨{targetPost with clock := targetPost.clock + (cost+reserve)}, ?_, by simp; omega, ?_⟩
  · simpa only [Nat.add_assoc] using boosted
  · simpa using compCorrectResult_setClocks ac k f frame source post targetPost result
      (some (.halt (.word 2))) lens post.clock relation


/-- The ordinary-call induction step composes explicit callee and continuation budgets. -/
theorem rateReturningNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (rate extra bodyCost contCost : Nat)
    (bodyFits : bodyCost ≤ rate+extra)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate contCost retCode t)
    (codeBudget : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac rate bodyCost p t) :
    RateSimulation ac rate (extra+contCost) (.call (some (values, names, retCode, l1, l2)) dest args none) source := by
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises reserve
  obtain ⟨execution, notError, notTimeout, related, conventions, flat, compilation, bitmapLength,
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
    · obtain ⟨get,bad,find,valid,cut⟩ := guards
      rw [WordSemStateFiniteExact.evaluate] at execution
      simp only [get,bad,Bool.false_eq_true,if_false,find,valid,cut] at execution
      rw [dif_pos zero] at execution
      exact (notTimeout (congrArg Prod.fst execution.symm)).elim
    · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
          else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace
      · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
          ⟨bodyResult, bodyPost⟩
        simpa only [Nat.add_assoc] using rateSuccessfulReturningCall ac k f frame values names retCode l1 l2 dest args source target
          lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex
          destinationCode savedCode returnCode compiled destination guards related conventions maximum
          destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound
          bitmapPrefix sourcePost bodyPost result bodyResult rate extra bodyCost contCost reserve bodyFits retBudget codeBudget zero execution notError notTimeout bodyRun calleeSpace
      · obtain ⟨calleeSize, _, sizeEq, failure⟩ := compiledCalleeFrameFailure ac k f frame values names
          retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
          returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
          related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound
          compiled compilation execution argumentsSpace zero bitmapPrefix
        obtain ⟨targetPost, run, conclusion⟩ := failure (by rw [sizeEq]; omega)
        obtain ⟨final,actual,enough,relation⟩ := resourceWithReserve ac k f frame source sourcePost target targetPost result compiled lens (rate*source.clock+extra+contCost) reserve (by simpa using run) (by simpa using conclusion)
        exact ⟨final,some (.halt (.word 2)),by simpa [Nat.add_assoc] using actual,enough,Or.inl rfl,relation⟩
  · obtain ⟨targetPost, run, conclusion⟩ := compiledStackArgumentsFailure ac k f frame values names
      retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
      returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related
      conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled
      compilation execution (by omega) bitmapPrefix
    obtain ⟨final,actual,enough,relation⟩ := resourceWithReserve ac k f frame source sourcePost target targetPost result compiled lens (rate*source.clock+extra+contCost) reserve (by simpa using run) (by simpa using conclusion)
    exact ⟨final,some (.halt (.word 2)),by simpa [Nat.add_assoc] using actual,enough,Or.inl rfl,relation⟩




theorem budgetReturningNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (bodyCost contCost : Nat)
    (retBudget : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac retCode t contCost)
    (codeBudget : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → BudgetSimulation ac p t bodyCost) :
    BudgetSimulation ac (.call (some (values, names, retCode, l1, l2)) dest args none) source (bodyCost + contCost) := by
  have retRate : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
      t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 contCost retCode t := by
    intro t smaller transfer
    exact budget_to_rate ac 0 contCost retCode t (retBudget t smaller transfer)
  have codeRate : ∀ loc arity p, sptLookup loc source.code = some (arity,p) →
      ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < source.clock → (safeWordCode source → safeWordCode t ∧ t.code = source.code) → RateSimulation ac 0 bodyCost p t := by
    intro loc arity p found t smaller transfer
    exact budget_to_rate ac 0 bodyCost p t (codeBudget loc arity p found t smaller transfer)
  have sim := rateReturningNone ac values names retCode l1 l2 dest args source 0 bodyCost bodyCost contCost (by omega) retRate codeRate
  simpa using rate_to_fixed_budget ac 0 (bodyCost+contCost) (.call (some (values,names,retCode,l1,l2)) dest args none) source sim

end SteppedFlapjack.WordToStackSteps
