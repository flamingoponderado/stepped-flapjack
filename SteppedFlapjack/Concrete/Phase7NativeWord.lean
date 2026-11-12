import SteppedFlapjack.Concrete.Phase7NativeFacts

/-! The supported Word call exposes the native compiler's tail entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordToStackSteps

set_option maxHeartbeats 1000000 in
/-- A counted supported source return reaches the actual selected native Word
entry, preserving FFI and satisfying the compiled-code visit bound. -/
theorem supported_counted_nativeWord
    (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (fuel count n : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (word : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL program)).structs []
      (executableState (progToHOL program)).baseAddress (executableState (progToHOL program)).topAddress
      panSemBitVec64BytesInWord fuel (executableState (progToHOL program)).locals
      (executableState (progToHOL program)).globals (executableState (progToHOL program)).memory
      (executableState (progToHOL program)).ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL program)))) =
        some (.returned postLocals postGlobals postMemory postFfi [.word word],count)) (countBound : count ≤ n)
    (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 (supportedNative program).2.2.2) :
    let words := supportedWordPrograms program
    let code := (supportedNative program).2.2.2
    let stack := fixtureStack code cfg
    let entry := nativeTailEntryWord countdownRiscVBackend.wordToWordConf riscvConfig words 64 supportedEntry
      stack (fixtureWordOracle cfg) (6*supportedLoopVisits program n)
    ∃ post, evaluate countdownOptimizedEntry entry = (some (.result (.loc 1 0) [.word word]),post) ∧
      WordSteps.steps countdownOptimizedEntry entry ≤ supportedWordBound program n ∧ FfiStateRel postFfi post.ffi := by
  let words := supportedWordPrograms program
  let code := (supportedNative program).2.2.2
  let allocated := (supportedAllocated program).2
  let stack := fixtureStack code cfg
  let wordState := fixtureWord code allocated cfg
  let clock := 6*supportedLoopVisits program n
  let wordStart := {wordState with clock := clock+1}
  let body := nativeTailEntryWord countdownRiscVBackend.wordToWordConf riscvConfig words 64 supportedEntry
    stack (fixtureWordOracle cfg) clock
  have facts := supported_nativeEntry_facts program supported cfg
  have alloc : allocated = (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2 := by
    have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    simp only [allocated,supportedAllocated,phase3WordConfig_eq,WordToWord.compileWith_eq_compile _ allocator]
    rfl
  obtain ⟨final,post,_,stateRel,result,ffi,bound,crepFfi⟩ := supported_counted_initializedWord program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound cfg 0 good facts.2.2.2.2
  have lookup : sptLookup 64 wordStart.code = some (1,countdownOptimizedEntry) := by
    change sptLookup 64 (sptFromAList allocated) = _
    rw [alloc]
    exact facts.2.2.1
  have frame : sptLookup 64 wordStart.stackSize = some 0 := facts.2.2.2.2
  have args : WordSemStateFiniteExact.getVars [0] wordStart = some [(.loc 1 0 : WordLocW 64)] := by
    simp [wordStart,wordState,fixtureWord,makeInit,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,sptLookup]
  have find : wordSemFindCode (some 64) [(.loc 1 0 : WordLocW 64)] wordStart.code wordStart.stackSize =
      some ([.loc 1 0],countdownOptimizedEntry,some 0) := by
    simp [wordSemFindCode,lookup,frame]
  have bodyEq : WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some 0) (WordSemStateFiniteExact.decClock wordStart) = body := by
    have selected := facts.2.2.2.1
    change nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig words 64 supportedEntry = countdownOptimizedEntry at selected
    simp only [body,nativeTailEntryWord,selected]
    have zero : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = 0 := by
      with_unfolding_all rfl
    rw [zero]
    simp [wordStart,wordState,fixtureWord,makeInit,alloc,clock,stack,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
  have callEq : WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) wordStart =
      let r := WordSemStateFiniteExact.evaluate countdownOptimizedEntry body
      if wordSemBadFunReturn r.1 then (some .error,r.2) else r := by
    rw [WordSemStateFiniteExact.evaluate]
    simp [args,wordSemBadDestArgs,wordSemAddRetLoc,find,show wordStart.clock ≠ 0 by simp [wordStart,clock],bodyEq]
  let entryPost := (evaluate countdownOptimizedEntry body).2
  have bodyResult : (evaluate countdownOptimizedEntry body).1 = some (.result (.loc 1 0) [.word word]) := by
    change (evaluate (.call none (some 64) [0] none) wordStart).1 = _ at result
    rw [callEq] at result
    dsimp only at result
    split at result
    · simp at result
    · exact result
  have runEntry : evaluate countdownOptimizedEntry body = (some (.result (.loc 1 0) [.word word]),entryPost) :=
    Prod.ext bodyResult rfl
  have entryFfi : entryPost.ffi = post.ffi := by
    change (evaluate (.call none (some 64) [0] none) wordStart).2.ffi = post.ffi at ffi
    rw [callEq,runEntry] at ffi
    simpa [wordSemBadFunReturn] using ffi
  have stepEq := WordSteps.steps_call_tail (some 64) [0] wordStart [.loc 1 0] [.loc 1 0] (some 0) countdownOptimizedEntry
    args rfl find (by simp [wordStart,clock])
  rw [bodyEq] at stepEq
  have bodyBound : WordSteps.steps countdownOptimizedEntry body ≤ supportedWordBound program n := by
    change WordSteps.steps (.call none (some 64) [0] none) wordStart ≤ _ at bound
    rw [stepEq] at bound
    omega
  have ffiEq : final.ffi = post.ffi := stateRel.2.2.2.2.1
  refine ⟨entryPost,runEntry,bodyBound,?_⟩
  rw [entryFfi,← ffiEq]
  exact crepFfi
end SteppedFlapjack.Concrete
