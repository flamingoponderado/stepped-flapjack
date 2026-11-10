import SteppedFlapjack.Concrete.CountdownNativeStarter
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete

theorem countdownFixture_callFind (n : Nat) (cfg : LabToTarget.Config) :
 wordSemFindCode (some 64) [(.loc 1 0 : WordLocW 64)] (countdownFixtureWord n cfg).code
    (countdownFixtureWord n cfg).stackSize = some ([.loc 1 0],countdownOptimizedEntry,some 0) := by
  have lookup : sptLookup 64 (countdownFixtureWord n cfg).code = some (1,countdownOptimizedEntry) := by
    change sptLookup 64 (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2) = _
    rw [countdown_optimized_literal,sptLookup_sptFromAList]
    simp [countdownOptimizedLiteral,countdownOptimizedEntry,sptAListLookup]
  simp [wordSemFindCode,lookup,countdownFixture_entryFrame]

theorem countdownFixture_callEq (n : Nat) (cfg : LabToTarget.Config) (clock : Nat) :
 let w := {(countdownFixtureWord n cfg) with clock := clock+1}
 let body := {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock}
 evaluate (.call none (some 64) [0] none) w =
   let r := evaluate countdownOptimizedEntry body
   if wordSemBadFunReturn r.1 then (some .error,r.2) else r := by
  dsimp only
  rw [evaluate]
  have args : getVars [0] {(countdownFixtureWord n cfg) with clock := clock+1} = some [(.loc 1 0 : WordLocW 64)] := by
    simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,countdownFixtureWord,fixtureWord,WordToStack.Native.Initialization.makeInit,sptLookup]
  have fn := countdownFixture_callFind n cfg
  simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,fn,show clock+1 ≠ 0 by omega,↓reduceDIte]
  rfl

open SteppedFlapjack.WordToStackSteps Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The counted source reaches the initialized native Stack entry with matching
result and FFI and a concrete, code-derived visit bound. -/
theorem countdownFixture_source_stack (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit) (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config Unit) (targetResult : Option (StackSemResult 64)),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState (countdown n)
        (clockedFixtureSource (countdown n) (6*n+9))) (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      targetPost.ffi = post.ffi ∧
      StackSemEvaluate.evaluate (.call none (.inl 64) none,
        {(countdownFixtureStack n cfg) with clock := countdownWordBound n+1}) = (targetResult,targetPost) ∧
      some (compileResult (.result (.loc 1 0) [.word 0])) = targetResult ∧
      SteppedFlapjack.StackSteps.steps (.call none (.inl 64) none,
        {(countdownFixtureStack n cfg) with clock := countdownWordBound n+1}) ≤
        nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) (countdownWordBound n) := by
  let clock := 6*countdownLoopVisits n
  let body := {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock}
  let word := {(countdownFixtureWord n cfg) with clock := clock+1}
  let entryPost := (evaluate countdownOptimizedEntry body).2
  obtain ⟨final,post,crepRun,stateRel,result,ffi,bound⟩ := countdownFixture_native_word n range cfg context primitive handler
  have result' : (evaluate (.call none (some 64) [0] none) word).1 = some (.result (.loc 1 0) [.word 0]) := result
  have bodyResult : (evaluate countdownOptimizedEntry body).1 = some (.result (.loc 1 0) [.word 0]) := by
    rw [countdownFixture_callEq n cfg clock] at result'
    dsimp only at result'
    split at result'
    · simp at result'
    · exact result'
  have run : evaluate countdownOptimizedEntry body = (some (.result (.loc 1 0) [.word 0]),entryPost) := by
    exact Prod.ext bodyResult rfl
  have entryFfi : entryPost.ffi = post.ffi := by
    change (evaluate (.call none (some 64) [0] none) word).2.ffi = post.ffi at ffi
    rw [countdownFixture_callEq n cfg clock,run] at ffi
    simpa [wordSemBadFunReturn] using ffi
  have args : getVars [0] word = some [(.loc 1 0 : WordLocW 64)] := by
    simp [word,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,countdownFixtureWord,fixtureWord,WordToStack.Native.Initialization.makeInit,sptLookup]
  have find : wordSemFindCode (some 64) [(.loc 1 0 : WordLocW 64)] word.code word.stackSize =
      some ([.loc 1 0],countdownOptimizedEntry,some 0) := countdownFixture_callFind n cfg
  have stepEq := WordSteps.steps_call_tail (some 64) [0] word [.loc 1 0] [.loc 1 0] (some 0) countdownOptimizedEntry
    args rfl find (by simp [word])
  have bodyEq : callEnv [(.loc 1 0 : WordLocW 64)] (some 0) (decClock word) = body := by
    simp [word,body,clock,countdownInitialWord,countdownFixtureWord,fixtureWord,countdownZeroLimit,RowColoring.limit,countdownFixtureStack,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
  rw [bodyEq] at stepEq
  have bodyBound : WordSteps.steps countdownOptimizedEntry body ≤ countdownWordBound n := by
    change WordSteps.steps (.call none (some 64) [0] none) word ≤ _ at bound
    rw [stepEq] at bound
    omega
  obtain ⟨targetPost,targetResult,targetRun,targetRel,targetFfi,targetBound⟩ :=
    countdownFixture_stack_span n clock (countdownWordBound n) cfg (some (.result (.loc 1 0) [.word 0])) entryPost
      run (by simp) (by simp) (.return [.word 0]) bodyBound
  exact ⟨final,post,targetPost,targetResult,crepRun,stateRel,targetFfi.symm.trans entryFfi,targetRun,targetRel,targetBound⟩
end SteppedFlapjack.Concrete
