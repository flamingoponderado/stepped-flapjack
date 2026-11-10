import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.Concrete.CountdownLoopSpan
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordToStack.Native

namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The witness Word table is the original Pancake compiler output. -/
theorem countdown_panToWord (n : Nat) :
    panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL (countdown n))) = countdownWordPrograms n := by
  have h := singleEntry_countdown_panToWord riscvConfig.isa (ofString "x") (BitVec.ofNat 64 n) 0
  have code := natural_countdown_crep_code n
  unfold crepPrograms declarations at code
  dsimp only at h
  simp only [naturalCountdownHOL,naturalCountdown,countdownBody,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil] at code
  rw [code] at h
  simpa [countdownWordPrograms,countdownCrepCode,twoPrograms,phase3CountdownCrepBody, countdown,progToHOL,expToHOL,shapeToHOL,countdownBody,naturalCountdownHOL,naturalCountdown] using h

/-- The original compiler guarantees the countdown Stack table is well formed. -/
theorem countdown_nativeGoodCode (n : Nat) : StackToLab.Proofs.GoodCode.goodCode 24
    (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2 := by
  exact singleEntry_nativeGoodCode (progToHOL (countdown n)) (countdownWordPrograms n) (countdown_panToWord n)

/-- Actual compiled Stack code for the countdown. -/
noncomputable def countdownNativeStackCode (n : Nat) : List (Nat × StackLang.HolProg 64) :=
  (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2

/-- Actual fullMakeInit Stack state for the countdown and concrete Lab layout. -/
noncomputable def countdownFixtureStack (n : Nat) (cfg : LabToTarget.Config) := fixtureStack (countdownNativeStackCode n) cfg

/-- Native initialization holds for the actual countdown Stack state. -/
theorem countdownFixture_initOk (n : Nat) (cfg : LabToTarget.Config) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (countdownFixtureStack n cfg) (fixtureWordOracle cfg) :=
  fixtureStack_nativeInitOk _ cfg (countdown_nativeGoodCode n)

open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps

/-- A bounded optimized countdown run simulates on the actual initialized Stack state. -/
theorem countdownFixture_stack_span (n clock limit : Nat) (cfg : LabToTarget.Config)
    (result : Option (WordSemResult 64)) (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit)
    (run : evaluate countdownOptimizedEntry {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock} = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (complete : CompleteWordResult result)
    (bound : SteppedFlapjack.WordSteps.steps countdownOptimizedEntry
      {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock} ≤ limit) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl 64) none,{(countdownFixtureStack n cfg) with clock := limit+1}) = (targetResult,targetPost) ∧
      result.map compileResult = targetResult ∧ post.ffi = targetPost.ffi ∧
      SteppedFlapjack.StackSteps.steps (.call none (.inl 64) none,{(countdownFixtureStack n cfg) with clock := limit+1}) ≤
        nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) limit := by
  apply countdown_stack_span n clock limit (countdownFixtureStack n cfg) (fixtureWordOracle cfg)
  · exact fixtureStack_code _ cfg
  · rw [countdown_native_bitmaps]
    change [4] <+: (fixtureStack (countdownNativeStackCode n) cfg).bitmaps
    rw [fixtureStack_bitmaps]
  · exact countdownFixture_initOk n cfg
  · exact fixtureStack_nonempty _ cfg
  · exact run
  · exact notError
  · exact notTimeout
  · exact complete
  · exact bound


/-- The counted countdown source reaches Loop code using the actual initialized
Stack memory, with an explicit Loop visit bound. -/
theorem countdownFixture_initialized_loop (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
    let target := {(loopStateFrom riscvConfig.isa source (naturalCountdownHOL n)) with
      memory := (countdownFixtureStack n cfg).memory}
    let ctxt := witnessLoopContext riscvConfig.isa (naturalCountdownHOL n)
    let bound := 156*(3 + 8*(6*n+18)+1)
    ∃ final post,
      evalCrepSemHOLProgExact (crepStateFrom source (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      (64,[],branchingLoopEntry) ∈ compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n)) ∧
      Flapjack.LoopSemStateFiniteExact.evaluate branchingLoopEntry {target with clock := target.clock+bound} =
        (some (.result [.word 0]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+bound} ≤
        52*(3 + 8*(6*n+18)+bound+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let source := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  obtain ⟨final,run,bound⟩ := countdown_counted_fixture n range context primitive handler
  have nonzero : (crepStateFrom source (naturalCountdownHOL n)).clock ≠ 0 := by
    simp [source,crepStateFrom,concreteDeclCrepState,panSimpSourceState,clockedFixtureSource,
      loweredStateFrom,noGlobalsLoweredPreCall]
  obtain ⟨post,compiled,entry,steps,state,mem,globals,codeRel⟩ :=
    naturalCountdown_entry_loop riscvConfig.isa source final n (3+8*(6*n+18))
      (countdownFixtureStack n cfg).memory (fixtureCrep_memory (countdown n) (6*n+9) (naturalCountdownHOL n)
        (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n)) nonzero run bound
  refine ⟨final,post,run,compiled,?_,?_,state,mem,globals,codeRel⟩
  · simpa only [countdown_optimized_weight] using entry
  · simpa only [countdown_optimized_weight] using steps


/-- The initialized-memory countdown Loop run reaches the optimized Word entry
with the same initialized memory and an explicit Word visit bound. -/
theorem countdownFixture_initialized_word (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit)
    (template : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit) (frame : Nat) :
    let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
    let crep := crepStateFrom pan (naturalCountdownHOL n)
    let starter := {(countdownWordStarter n template frame) with memory := (countdownFixtureStack n cfg).memory}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*countdownLoopVisits n+1, code := sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2}
    ∃ (final : CrepSemHOLState 64 Unit) (post : Flapjack.LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 0]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*countdownLoopVisits n+1, code := sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2} ≤
        countdownWordBound n := by
  let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  let crep := crepStateFrom pan (naturalCountdownHOL n)
  let timed := {crep with clock := crep.clock + countdownLoopBudget n}
  let memory := (countdownFixtureStack n cfg).memory
  have code : crepPrograms (naturalCountdownHOL n) = countdownCrepCode n := by
    simpa [countdownCrepCode,phase3CountdownCrepBody,twoPrograms] using natural_countdown_crep_code n
  obtain ⟨final,post,crepRun,_,loopRun,loopBound,stateRel,_,_,_⟩ :=
    countdownFixture_initialized_loop n range cfg context primitive handler
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap (countdown n) (6*n+9) (naturalCountdownHOL n)
  have loopEq : {(concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) with memory := memory} =
      {(loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n)) with memory := memory, clock := (loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n)).clock + countdownLoopBudget n} := by
    simp [timed,crep,pan,loopStateFrom,concreteDeclLoopState,code]
  have sourceRun : Flapjack.LoopSemStateFiniteExact.evaluate branchingLoopEntry
      {(concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) with memory := memory} =
      (some (.result [.word 0]),post) := by
    rw [loopEq]
    simpa [pan,memory,countdownLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry
      {(concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) with memory := memory} ≤ countdownLoopVisits n := by
    rw [loopEq]
    simpa [pan,memory,countdownLoopBudget,countdownLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n))) (naturalCountdown_scalar n)
    timed post [.word 0] (countdownLoopVisits n) template fixtureHeapLength frame
    countdownRiscVBackend.wordToWordConf riscvConfig memory heap sourceRun sourceBound
  obtain ⟨_,wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨final,post,?_,stateRel,?_,?_,?_⟩
  · simpa [crep,pan] using crepRun
  · simpa [countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan,memory,relation.2.1] using result
  · simpa [countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan,memory] using ffi
  · simpa [countdownWordBound,phase3WordConfig_eq,countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan,memory] using bound

end SteppedFlapjack.Concrete
