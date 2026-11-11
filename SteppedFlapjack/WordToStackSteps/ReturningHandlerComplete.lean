import SteppedFlapjack.WordToStackSteps.ReturningHandlerZeroClock
import SteppedFlapjack.WordToStackSteps.ReturningNoneComplete

/-! Source-step bounds for returning calls with handlers. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Count source clock consumption for every non-timeout handler call. -/
theorem returningHandler_consumed {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F) (result : Option (WordSemResult width))
    (retBlock : LoopBlock retCode) (handlerBlock : LoopBlock handlerCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (run : WordSemStateFiniteExact.evaluate (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source = (result, sourcePost))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut) :
    source.clock - sourcePost.clock ≤ WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source := by
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotErrorWithHandler values names retCode l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) source sourcePost result run notError
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
    (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) with ⟨bodyResult, bodyPost⟩
  obtain ⟨loc, lookup, _, _, _⟩ := CallTail.findCode_facts dest
    (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) xs) source.code source.stackSize args1 prog ss find
  have bodyShape := loopBlock_loop (code loc args1.length prog lookup)
  have bodyClock := WordSteps.loopWord_consumption prog
    (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) bodyShape
  rw [bodyRun] at bodyClock
  have entryClock : (WordSemStateFiniteExact.callEnv args1 ss
      (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))).clock = source.clock - 1 := by
    simp [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, WordSemStateFiniteExact.decClock]
  rw [entryClock] at bodyClock
  have stepEquation := WordSteps.steps_call_returning dest args values names retCode l1 l2 (some (handlerVar,handlerCode,h1,h2)) source bodyPost bodyResult
    xs args1 ss prog envs get badFalse find valid cut nonzero bodyRun
  have bodyCost : source.clock - 1 ≤ bodyPost.clock + WordSteps.steps prog
      (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) := bodyClock
  have terminalBound (samePost : sourcePost = bodyPost) :
      source.clock - sourcePost.clock ≤ WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source := by
    rw [samePost, stepEquation]
    omega
  have outcomes := handlerCalleeOutcomeCases values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult
    xs args1 prog ss envs guards nonzero run bodyRun notError
  rcases outcomes with ⟨location, returned, hr⟩ | ⟨location, value, he⟩ | ht | hs | ⟨event, hf⟩
  · subst bodyResult
    have ih := handlerOriginalIH ac values names retCode handlerCode l1 l2 dest args handlerVar h1 h2 source
    obtain ⟨_, _, popped, _, _, _, _, _, pop, domain, validReturn, _, _⟩ :=
      sourceHandlerReturningContinuation ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost result
        xs args1 prog ss envs location returned guards ih nonzero run notError bodyRun
    have locationEq : location = .loc l1 l2 := by tauto
    have lengthEq : returned.length = values.length := by tauto
    subst location
    exact WordSteps.returningCall_consumed dest args values names retCode l1 l2 (some (handlerVar,handlerCode,h1,h2)) source bodyPost popped sourcePost result
      xs args1 returned ss prog envs bodyShape (loopBlock_loop retBlock) get badFalse find valid cut nonzero bodyRun lengthEq pop domain run
  · subst bodyResult
    have ih := handlerOriginalIH ac values names retCode handlerCode l1 l2 dest args handlerVar h1 h2 source
    obtain ⟨validException, domain, _, _⟩ := sourceHandlerExceptionContinuation ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost result xs args1 prog ss envs location value guards ih nonzero run notError bodyRun
    have locationEq : location = .loc h1 h2 := by tauto
    subst location
    exact WordSteps.returningCall_exception_consumed dest args values names retCode l1 l2 handlerVar handlerCode h1 h2 source bodyPost sourcePost result xs args1 ss prog envs value bodyShape (loopBlock_loop handlerBlock) get badFalse find valid cut nonzero bodyRun domain run
  · exact terminalBound (handlerSourceCallTerminal values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inl ht)).2
  · exact terminalBound (handlerSourceCallTerminal values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inr (Or.inl hs))).2
  · exact terminalBound (handlerSourceCallTerminal values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost result bodyResult
      xs args1 prog ss envs guards nonzero run bodyRun (Or.inr (Or.inr ⟨event, hf⟩))).2



/-- A source-step limit yields an actual compiled handler-call execution and bound. -/
theorem returningHandler_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat) (retBlock : LoopBlock retCode) (handlerBlock : LoopBlock handlerCode)
    (code : ∀ loc arity p, sptLookup loc source.code = some (arity, p) → LoopBlock p)
    (notTimeout : result ≠ some .timeOut)
    (stepBound : WordSteps.steps (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true ∧
      flatExpConventions (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true ∧
      compNative ac false (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens ∧
      StackSteps.steps (compiled, {target with clock := limit}) ≤ returningChainCost limit target.code compiled := by
  have used := returningHandler_consumed ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost result
    retBlock handlerBlock code premises.1 premises.2.1 notTimeout
  have normalized := normalize_of_consumed (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2)))
    source sourcePost result limit premises.1 notTimeout (used.trans stepBound)
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity p, sptLookup loc ({source with clock := limit}).code = some (arity, p) → LoopBlock p := code
  have sim := zeroReturningHandlerCase ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode {source with clock := limit}
    (fun t _ _ => loopBlock_zero ac retCode t retBlock)
    (fun t _ _ => loopBlock_zero ac handlerCode t handlerBlock)
    (fun loc arity p lookup t _ _ => loopBlock_zero ac p t (normalizedCode loc arity p lookup))
  obtain ⟨targetPost, targetResult, targetRun, conclusion⟩ := sim k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit} result
    bs bsPost n nPost compiled lens ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have bound := compiledReturning_related_bound ac values names retCode l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) (bs, n) k f frame lens
    {source with clock := limit} {target with clock := limit} related normalizedCode retBlock (by intro v p a b h; cases h; exact handlerBlock)
  rw [premises.2.2.2.2.2.1] at bound
  exact ⟨targetPost, targetResult, targetRun, conclusion, bound⟩


end SteppedFlapjack.WordToStackSteps
