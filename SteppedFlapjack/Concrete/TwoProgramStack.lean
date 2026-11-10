import SteppedFlapjack.Concrete.BranchingFrames
import SteppedFlapjack.Concrete.CountdownSourceStack
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.WordSemStateFiniteExact
open Flapjack.WordToStackProofs.CompCorrect Flapjack.WordToStackProofs.InitializationStateRel
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
namespace SteppedFlapjack.Concrete

/-- A scalar two-function source fixture reaches its initialized Stack entry
with the Word result and an explicit code-derived Stack visit bound. -/
theorem twoProgram_fixture_stack
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) (shape : ScalarProgram body)
    (cfg : LabToTarget.Config) (clock limit : Nat) (value : BitVec 64)
    (good : StackToLab.Proofs.GoodCode.goodCode 24
      (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body)))).2).2.2.2)
    (calleeFrame : let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
      let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
      let code := (compileNative riscvConfig false words).2.2.2
      sptLookup 65 (fixtureWord code words cfg).stackSize = some 0)
    (result : let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
      let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
      let code := (compileNative riscvConfig false words).2.2.2
      (evaluate (.call none (some 64) [0] none) {(fixtureWord code words cfg) with clock := clock+1}).1 =
        some (.result (.loc 1 0) [.word value]))
    (bound : let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
      let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
      let code := (compileNative riscvConfig false words).2.2.2
      WordSteps.steps (.call none (some 64) [0] none) {(fixtureWord code words cfg) with clock := clock+1} ≤ limit) :
    let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
    let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
    let code := (compileNative riscvConfig false words).2.2.2
    let stack := fixtureStack code cfg
    let word := {(fixtureWord code words cfg) with clock := clock+1}
    let entry := loopToWordCompFuncHOL 64 [] branchingLoopEntry
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl 64) none,{stack with clock := limit+1}) = (targetResult,targetPost) ∧
      targetResult = some (compileResult (.result (.loc 1 0) [.word value])) ∧
      targetPost.ffi = (evaluate (.call none (some 64) [0] none) word).2.ffi ∧
      StackSteps.steps (.call none (.inl 64) none,{stack with clock := limit+1}) ≤
        nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig programs 64 entry limit := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
  let words := (compile countdownRiscVBackend.wordToWordConf riscvConfig programs).2
  let code := (compileNative riscvConfig false words).2.2.2
  let stack := fixtureStack code cfg
  let word := fixtureWord code words cfg
  let entry := loopToWordCompFuncHOL 64 [] branchingLoopEntry
  let entryWord := {(callEnv [(.loc 1 0 : WordLocW 64)] (some 0) word) with clock := clock}
  have table := twoWordTables_facts arch name callee body fresh shape
  have loopEq := (twoLoopPrograms_eq arch name callee body shape).symm
  have member : (64,1,entry) ∈ programs := by simpa [programs,entry,loopEq] using table.1
  have nodup : (programs.map Prod.fst).Nodup := by simpa [programs,loopEq] using table.2.2.1
  have lookup : sptLookup 64 word.code = some (1,countdownOptimizedEntry) := by
    exact twoProgram_optimizedEntry_lookup arch name callee body fresh shape
  have frame : sptLookup 64 word.stackSize = some 0 :=
    twoProgram_optimizedEntry_frame arch name callee body fresh shape code cfg
  have selected : nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig programs 64 entry = countdownOptimizedEntry := by
    exact twoProgram_selectedEntry arch name callee body fresh shape
  have zeroEntry : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = 0 := by
    with_unfolding_all rfl
  have wordEq : nativeTailEntryWord countdownRiscVBackend.wordToWordConf riscvConfig programs 64 entry stack (fixtureWordOracle cfg) clock = entryWord := by
    simp only [nativeTailEntryWord,selected,zeroEntry,entryWord,word,fixtureWord,stack]
    rfl
  have args : getVars [0] {word with clock := clock+1} = some [(.loc 1 0 : WordLocW 64)] := by
    simp [word,fixtureWord,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,WordToStack.Native.Initialization.makeInit,sptLookup]
  have find : wordSemFindCode (some 64) [(.loc 1 0 : WordLocW 64)] word.code word.stackSize =
      some ([.loc 1 0],countdownOptimizedEntry,some 0) := by simp [wordSemFindCode,lookup,frame]
  have callEq : evaluate (.call none (some 64) [0] none) {word with clock := clock+1} =
      let r := evaluate countdownOptimizedEntry entryWord
      if wordSemBadFunReturn r.1 then (some .error,r.2) else r := by
    rw [evaluate]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,find,show clock+1 ≠ 0 by omega,↓reduceDIte]
    rfl
  have bodyResult : (evaluate countdownOptimizedEntry entryWord).1 = some (.result (.loc 1 0) [.word value]) := by
    change (evaluate (.call none (some 64) [0] none) {word with clock := clock+1}).1 = _ at result
    rw [callEq] at result
    dsimp only at result
    split at result <;> simp_all
  have bodyRun : evaluate countdownOptimizedEntry entryWord =
      (some (.result (.loc 1 0) [.word value]),(evaluate countdownOptimizedEntry entryWord).2) := Prod.ext bodyResult rfl
  have bodyFfi : (evaluate countdownOptimizedEntry entryWord).2.ffi =
      (evaluate (.call none (some 64) [0] none) {word with clock := clock+1}).2.ffi := by
    rw [callEq,bodyRun]
    simp [wordSemBadFunReturn]
  have stepEq := WordSteps.steps_call_tail (some 64) [0] {word with clock := clock+1} [.loc 1 0] [.loc 1 0] (some 0) countdownOptimizedEntry args rfl find (by simp)
  have bodyEq : callEnv [(.loc 1 0 : WordLocW 64)] (some 0) (decClock {word with clock := clock+1}) = entryWord := by
    simp [entryWord,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
  rw [bodyEq] at stepEq
  have bodyBound : WordSteps.steps countdownOptimizedEntry entryWord ≤ limit := by
    change WordSteps.steps (.call none (some 64) [0] none) {word with clock := clock+1} ≤ limit at bound
    rw [stepEq] at bound
    omega
  have noRaise : raiseStubLocation ∉ programs.map Prod.fst := by
    rw [show programs = loopToWordCompileHOL (twoLoopPrograms arch name callee body) from congrArg loopToWordCompileHOL loopEq]
    rw [twoLoops_exact arch name callee body fresh]
    simp [loopToWordCompileHOL,loopToWordCompileProgHOL,raiseStubLocation,wordNumStubs,stackNumStubs]
  have noStore : storeConstsStubLocation ∉ programs.map Prod.fst := by
    rw [show programs = loopToWordCompileHOL (twoLoopPrograms arch name callee body) from congrArg loopToWordCompileHOL loopEq]
    rw [twoLoops_exact arch name callee body fresh]
    simp [loopToWordCompileHOL,loopToWordCompileProgHOL,storeConstsStubLocation,wordNumStubs,stackNumStubs]
  have facts := twoProgram_optimizedCallee arch name callee body fresh shape
  have reachableFrame : ∀ arity calleeProg, sptLookup 65 word.code = some (arity,calleeProg) →
      (compileProgNative riscvConfig false calleeProg arity (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 = 0 := by
    intro arity calleeProg found
    change sptLookup 65 (sptMapi _ word.code) = some 0 at calleeFrame
    rw [sptLookupMapi,found] at calleeFrame
    exact Option.some.inj calleeFrame
  obtain ⟨targetPost,targetResult,targetRun,targetResultEq,targetFfi,targetBound⟩ :=
    nativeTailEntry_span countdownRiscVBackend.wordToWordConf riscvConfig programs 64 entry member nodup stack (fixtureWordOracle cfg)
      noRaise noStore (fixtureStack_code _ cfg) (by rw [show programs = loopToWordCompileHOL (twoLoopPrograms arch name callee body) from congrArg loopToWordCompileHOL loopEq, twoWordTables_native_bitmaps arch name callee body fresh shape countdownRiscVBackend.wordToWordConf riscvConfig]; change [4] <+: (fixtureStack code cfg).bitmaps; rw [fixtureStack_bitmaps])
      (fixtureStack_nativeInitOk _ cfg good) (by rw [selected,zeroEntry]; omega) clock limit
      (some (.result (.loc 1 0) [.word value])) (evaluate countdownOptimizedEntry entryWord).2
      (by rw [selected]; exact countdownEntry_shape) (by rw [selected]; exact countdownEntry_noInstall)
      (by rw [wordEq]; exact facts.1) (by rw [selected,wordEq]; exact facts.2)
      (by rw [selected]; exact countdownEntry_convention) (by rw [selected]; exact countdownEntry_flat)
      (by rw [selected,wordEq]; exact bodyRun) (by simp) (by simp) (.return [.word value])
      (by
        constructor
        · rw [selected,zeroEntry]; exact fixtureStack_nonempty _ cfg
        · intro loc call arity calleeProg found
          have eq : loc = 65 := by rw [selected] at call; cases call with | left h => cases h | right h => cases h; rfl
          subst loc
          rw [reachableFrame arity calleeProg found]
          exact fixtureStack_nonempty _ cfg)
      (by rw [selected,wordEq]; exact bodyBound)
  exact ⟨targetPost,targetResult,targetRun,targetResultEq.symm,targetFfi.symm.trans bodyFfi,targetBound⟩
end SteppedFlapjack.Concrete
