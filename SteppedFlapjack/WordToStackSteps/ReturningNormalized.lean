import SteppedFlapjack.WordSteps.ReturningClock
import SteppedFlapjack.WordToStackSteps.ReturningPrefixSteps

/-! Source-step clock normalization for returning calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width]

/-- Any non-timeout WordSem run can be replayed with a clock that covers its
actual consumption, preserving the result and non-clock state. -/
theorem normalize_of_consumed {C F : Type} (p : WordLangProgHOL (BitVec width))
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (limit : Nat)
    (run : evaluate p s = (res, post)) (notTimeout : res ≠ some .timeOut)
    (enough : s.clock - post.clock ≤ limit) :
    evaluate p {s with clock := limit} = (res, {post with clock := limit - (s.clock - post.clock)}) := by
  have reduced := evaluate_dec_clock p s res post run
  have extended := evaluate_add_clock (limit - (s.clock - post.clock)) p
    {s with clock := s.clock - post.clock} res {post with clock := 0} ⟨reduced, notTimeout⟩
  have eqn : s.clock - post.clock + (limit - (s.clock - post.clock)) = limit := by omega
  simpa only [eqn, Nat.zero_add] using extended

/-- A normal returning call can be replayed with its source-step bound as the
clock; the actual compiled target execution at the related clock has a finite
structural bound. Target outcome preservation is not claimed here. -/
theorem normalReturn_normalized_target_bound {C F : Type} (ac : AsmConfigExact width)
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source middle restored post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (xs values ys : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs : AppList (BitVec width) × Nat) (k f frame limit : Nat) (lens : List Nat)
    (related : stateRel ac k f frame source target lens 0)
    (code : ∀ loc arity prog, sptLookup loc source.code = some (arity, prog) → LoopBlock prog)
    (retBlock : LoopBlock continuation)
    (handlerBlock : ∀ v p a b, handler = some (v, p, a, b) → LoopBlock p)
    (hargs : getVars args source = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      source.code source.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts source.locals = some envs) (hclock : source.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs handler (decClock source))) =
      (some (.result (.loc l1 l2) ys), middle)) (hlen : ys.length = names.length)
    (pop : popEnv middle = some restored) (hdom : sptDomainEqUnion restored.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args handler) source = (result, post))
    (notTimeout : result ≠ some .timeOut)
    (stepBound : WordSteps.steps (.call (some (names, cuts, continuation, l1, l2)) dest args handler) source ≤ limit) :
    evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args handler) {source with clock := limit} =
      (result, {post with clock := limit - (source.clock - post.clock)}) ∧
    StackSteps.steps ((compNative ac false (.call (some (names, cuts, continuation, l1, l2)) dest args handler) bs (k, f, frame)).1,
      {target with clock := limit}) ≤
      returningChainCost limit target.code
        (compNative ac false (.call (some (names, cuts, continuation, l1, l2)) dest args handler) bs (k, f, frame)).1 := by
  obtain ⟨loc, found, _, _, _⟩ := Flapjack.WordToStackProofs.CompCorrect.CallTail.findCode_facts dest
    (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs) source.code source.stackSize values callee ss hfind
  have consumed := returningCall_consumed dest args names cuts continuation l1 l2 handler source middle restored post
    result xs values ys ss callee envs (loopBlock_loop (code loc values.length callee found)) (loopBlock_loop retBlock)
    hargs hbad hfind hvalid hcut hclock bodyRun hlen pop hdom run
  have normalized := normalize_of_consumed _ source post result limit run notTimeout (consumed.trans stepBound)
  have targetRelated := stateRel_setClocks ac k f frame source target lens 0 limit related
  have normalizedCode : ∀ loc arity prog, sptLookup loc ({source with clock := limit}).code = some (arity, prog) → LoopBlock prog := code
  have bound := compiledReturning_related_bound ac names cuts continuation l1 l2 dest args handler bs k f frame lens
    {source with clock := limit} {target with clock := limit} targetRelated normalizedCode retBlock handlerBlock
  exact ⟨normalized, bound⟩


/-- The same normalized target bound for a matching exception-handler path. -/
theorem exceptionReturn_normalized_target_bound {C F : Type} (ac : AsmConfigExact width)
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (v : Nat) (hprog : WordLangProgHOL (BitVec width)) (hl1 hl2 : Nat)
    (source middle post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (value : WordLocW width)
    (bs : AppList (BitVec width) × Nat) (k f frame limit : Nat) (lens : List Nat)
    (related : stateRel ac k f frame source target lens 0)
    (code : ∀ loc arity prog, sptLookup loc source.code = some (arity, prog) → LoopBlock prog)
    (retBlock : LoopBlock continuation) (handlerBlock : LoopBlock hprog)
    (hargs : getVars args source = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      source.code source.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts source.locals = some envs) (hclock : source.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock source))) =
      (some (.exception (.loc hl1 hl2) value), middle))
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) source = (result, post))
    (notTimeout : result ≠ some .timeOut)
    (stepBound : WordSteps.steps (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) source ≤ limit) :
    evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) {source with clock := limit} =
      (result, {post with clock := limit - (source.clock - post.clock)}) ∧
    StackSteps.steps ((compNative ac false (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) bs (k, f, frame)).1,
      {target with clock := limit}) ≤
      returningChainCost limit target.code
        (compNative ac false (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) bs (k, f, frame)).1 := by
  obtain ⟨loc, found, _, _, _⟩ := Flapjack.WordToStackProofs.CompCorrect.CallTail.findCode_facts dest
    (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs) source.code source.stackSize values callee ss hfind
  have consumed := returningCall_exception_consumed dest args names cuts continuation l1 l2 v hprog hl1 hl2
    source middle post result xs values ss callee envs value (loopBlock_loop (code loc values.length callee found))
    (loopBlock_loop handlerBlock) hargs hbad hfind hvalid hcut hclock bodyRun hdom run
  have normalized := normalize_of_consumed _ source post result limit run notTimeout (consumed.trans stepBound)
  have targetRelated := stateRel_setClocks ac k f frame source target lens 0 limit related
  have normalizedCode : ∀ loc arity prog, sptLookup loc ({source with clock := limit}).code = some (arity, prog) → LoopBlock prog := code
  have handlers : ∀ v' p a b, some (v, hprog, hl1, hl2) = some (v', p, a, b) → LoopBlock p := by
    intro v' p a b eq
    cases eq
    exact handlerBlock
  have bound := compiledReturning_related_bound ac names cuts continuation l1 l2 dest args (some (v, hprog, hl1, hl2)) bs k f frame lens
    {source with clock := limit} {target with clock := limit} targetRelated normalizedCode retBlock handlers
  exact ⟨normalized, bound⟩

end SteppedFlapjack.WordToStackSteps
