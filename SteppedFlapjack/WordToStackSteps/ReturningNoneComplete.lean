import SteppedFlapjack.WordToStackSteps.ReturningNoneSteps

/-! Source clock bounds for all non-timeout no-handler returning calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Every non-error, non-timeout no-handler returning call into loop-block
code consumes no more WordSem clock than its actual counted source steps. -/
theorem returningNone_consumed {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F) (result : Option (WordSemResult width))
    (retBlock : LoopBlock retCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (run : WordSemStateFiniteExact.evaluate (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut) :
    source.clock - sourcePost.clock ≤ WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args none) source := by
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotError values names retCode l1 l2 dest args source sourcePost result run notError
  have ⟨get, bad, find, valid, cut⟩ := guards
  have badFalse : wordSemBadDestArgs dest args = false := by
    cases h : wordSemBadDestArgs dest args <;> simp_all
  have nonzero : source.clock ≠ 0 := by
    intro zero
    have e := run
    rw [WordSemStateFiniteExact.evaluate] at e
    simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut, dif_pos zero] at e
    exact notTimeout (congrArg Prod.fst e.symm)
  rcases bodyRun : WordSemStateFiniteExact.evaluate prog
    (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with ⟨bodyResult, bodyPost⟩
  obtain ⟨loc, lookup, _, _, _⟩ := CallTail.findCode_facts dest
    (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) source.code source.stackSize args1 prog ss find
  have bodyShape := loopBlock_loop (code loc args1.length prog lookup)
  have bodyClock := WordSteps.loopWord_consumption prog
    (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) bodyShape
  rw [bodyRun] at bodyClock
  have entryClock : (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))).clock = source.clock - 1 := by
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock]
  rw [entryClock] at bodyClock
  have stepEquation := WordSteps.steps_call_returning dest args values names retCode l1 l2 none source bodyPost bodyResult
    xs args1 ss prog envs get badFalse find valid cut nonzero bodyRun
  have bodyCost : source.clock - 1 ≤ bodyPost.clock + WordSteps.steps prog
      (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) := bodyClock
  have terminalBound (samePost : sourcePost = bodyPost) :
      source.clock - sourcePost.clock ≤ WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args none) source := by
    rw [samePost, stepEquation]
    omega
  have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult
    xs args1 prog ss envs guards nonzero run bodyRun notError
  rcases outcomes with ⟨location, returned, hr⟩ | ⟨location, value, he⟩ | ht | hs | ⟨event, hf⟩
  · subst bodyResult
    have ih := returningOriginalIH_of_blocks ac values names retCode l1 l2 dest args source retBlock code
    obtain ⟨_, _, popped, _, _, _, _, _, pop, domain, validReturn, _, _⟩ :=
      sourceReturningContinuation ac values names retCode l1 l2 dest args source sourcePost bodyPost result
        xs args1 prog ss envs location returned guards ih nonzero run notError bodyRun
    have locationEq : location = .loc l1 l2 := by tauto
    have lengthEq : returned.length = values.length := by tauto
    subst location
    exact WordSteps.returningCall_consumed dest args values names retCode l1 l2 none source bodyPost popped sourcePost result
      xs args1 returned ss prog envs bodyShape (loopBlock_loop retBlock) get badFalse find valid cut nonzero bodyRun lengthEq pop domain run
  · subst bodyResult
    exact terminalBound (sourceCallException values names retCode l1 l2 dest args source sourcePost bodyPost result
      location value xs args1 prog ss envs guards nonzero run bodyRun).2
  · exact terminalBound (sourceCallTerminal values names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inl ht)).2
  · exact terminalBound (sourceCallTerminal values names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inr (Or.inl hs))).2
  · exact terminalBound (sourceCallTerminal values names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inr (Or.inr ⟨event, hf⟩))).2


/-- Every non-timeout no-handler returning call into loop-block code has an
actual compiled execution with the original result relation, bounded by a
computable function of the source-step limit and compiled code. -/
theorem returningNone_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat) (retBlock : LoopBlock retCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (notTimeout : result ≠ some .timeOut)
    (stepBound : WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args none) source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate (.call (some (values, names, retCode, l1, l2)) dest args none) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.call (some (values, names, retCode, l1, l2)) dest args none) = true ∧
      flatExpConventions (.call (some (values, names, retCode, l1, l2)) dest args none) = true ∧
      compNative ac false (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := limit}) ≤ returningChainCost limit target.code compiled := by
  have used := returningNone_consumed ac values names retCode l1 l2 dest args source sourcePost result
    retBlock code premises.1 premises.2.1 notTimeout
  have normalized := normalize_of_consumed (.call (some (values, names, retCode, l1, l2)) dest args none)
    source sourcePost result limit premises.1 notTimeout (used.trans stepBound)
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity p, sptLookup loc ({source with clock := limit}).code = some (arity, p) → LoopBlock p := code
  have sim := zeroReturningNone ac values names retCode l1 l2 dest args {source with clock := limit} retBlock normalizedCode
  obtain ⟨targetPost, targetResult, targetRun, conclusion⟩ := sim k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit} result
    bs bsPost n nPost compiled lens ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have bound := compiledReturning_related_bound ac values names retCode l1 l2 dest args none (bs, n) k f frame lens
    {source with clock := limit} {target with clock := limit} related normalizedCode retBlock (by simp)
  rw [premises.2.2.2.2.2.1] at bound
  exact ⟨targetPost, targetResult, targetRun, conclusion, bound⟩

end SteppedFlapjack.WordToStackSteps
