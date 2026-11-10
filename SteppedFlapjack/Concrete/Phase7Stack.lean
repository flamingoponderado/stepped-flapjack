import SteppedFlapjack.Concrete.Phase7NativeWord

/-! Compose supported source execution through native Stack compilation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

/-- Explicit Stack visit budget derived from the generated native code. -/
noncomputable def supportedStackBound (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program) 64
    supportedEntry (supportedWordBound program n)

set_option maxHeartbeats 1000000 in
/-- The counted source return reaches the actual initialized native Stack
entry with a compiled-code bound and matching FFI state. -/
theorem supported_counted_nativeStack
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
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
    (good : StackToLab.Proofs.GoodCode.goodCode 24 (supportedNative program).2.2.2)
    (bitmap : (supportedNative program).1 = [4])
    (calleeFits : ∀ arity callee,
      sptLookup 65 (sptFromAList (supportedAllocated program).2) = some (arity,callee) →
      1 + (compileProgNative riscvConfig false callee arity (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 ≤
        (fixtureStack (supportedNative program).2.2.2 cfg).stack.length) :
    let code := (supportedNative program).2.2.2
    ∃ post, StackSemEvaluate.evaluate (.call none (.inl 64) none,
      {(fixtureStack code cfg) with clock := supportedWordBound program n+1}) = (some (.result (.loc 1 0)),post) ∧
      StackSteps.steps (.call none (.inl 64) none,
        {(fixtureStack code cfg) with clock := supportedWordBound program n+1}) ≤ supportedStackBound program n ∧
      FfiStateRel postFfi post.ffi := by
  let words := supportedWordPrograms program
  let code := (supportedNative program).2.2.2
  let stack := fixtureStack code cfg
  let entry := supportedEntry
  let wc := countdownRiscVBackend.wordToWordConf
  let clock := 6*supportedLoopVisits program n
  let limit := supportedWordBound program n
  have facts := supported_nativeEntry_facts program supported cfg
  have selected : nativeTailEntryCode wc riscvConfig words 64 entry = countdownOptimizedEntry := facts.2.2.2.1
  let simple := panSimpProg program
  let body := progToHOL simple
  let callee := supportedCallee body
  have shape := supportedCallee_scalar simple (supported_panSimp program supported).1
  have creps := supported_crepPrograms simple (supported_panSimp program supported).1
  have fresh : ofString "main" ≠ entryName body := Ne.symm (entryName_fresh body)
  have loops := (twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName body) callee shape).symm
  have loopRows := twoLoops_exact riscvConfig.isa (ofString "main") (entryName body) callee fresh
  have rows : words = [(64,1,entry),(65,1,loopToWordCompFuncHOL 65 [] (twoCallee riscvConfig.isa (ofString "main") (entryName body) callee))] := by
    change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms body)) = _
    rw [creps,loops,loopRows]
    rfl
  have noRaise : raiseStubLocation ∉ words.map Prod.fst := by simp [rows,raiseStubLocation,wordNumStubs,stackNumStubs]
  have noStore : storeConstsStubLocation ∉ words.map Prod.fst := by simp [rows,storeConstsStubLocation,wordNumStubs,stackNumStubs]
  have alloc : (supportedAllocated program).2 = (WordToWord.compile wc riscvConfig words).2 := by
    have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    simp only [supportedAllocated,phase3WordConfig_eq,WordToWord.compileWith_eq_compile _ allocator]
    rfl
  have codeEq : stack.code = sptFromAList (compileNative riscvConfig false (WordToWord.compile wc riscvConfig words).2).2.2.2 := by
    rw [fixtureStack_code]
    change sptFromAList (compileNative riscvConfig false (supportedAllocated program).2).2.2.2 = _
    rw [alloc]
  have bitmaps : (compileNative riscvConfig false (WordToWord.compile wc riscvConfig words).2).1.IsPrefix stack.bitmaps := by
    rw [← alloc]
    change (supportedNative program).1.IsPrefix (fixtureStack code cfg).bitmaps
    rw [bitmap,fixtureStack_bitmaps]
  have init := fixtureStack_nativeInitOk code cfg good
  have frameZero : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = 0 := by
    with_unfolding_all rfl
  have fits : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
      (nativeTailEntryCode wc riscvConfig words 64 entry) ≤ stack.stackSpace := by rw [selected,frameZero]; omega
  have codeFacts := twoProgram_optimizedCallee riscvConfig.isa (ofString "main") (entryName body) callee fresh shape
  have codeFacts' : WordProps.noInstallCode (sptFromAList (WordToWord.compile wc riscvConfig words).2) ∧
      RegTailLocalCode countdownOptimizedEntry (sptFromAList (WordToWord.compile wc riscvConfig words).2) := by
    change WordProps.noInstallCode (sptFromAList (WordToWord.compile wc riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms body)))).2) ∧
      RegTailLocalCode countdownOptimizedEntry (sptFromAList (WordToWord.compile wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms body)))).2)
    rw [creps]
    exact codeFacts
  obtain ⟨wordPost,wordRun,wordBound,wordFfi⟩ := supported_counted_nativeWord program supported
    context primitive handler fuel count n postLocals postGlobals postMemory postFfi word run countBound cfg good
  have frames : 1 + nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
        (nativeTailEntryCode wc riscvConfig words 64 entry) ≤ stack.stack.length ∧
      ∀ loc, RegTailCalls (nativeTailEntryCode wc riscvConfig words 64 entry) loc →
        ∀ arity callee, sptLookup loc (sptFromAList (WordToWord.compile wc riscvConfig words).2) = some (arity,callee) →
          1 + (compileProgNative riscvConfig false callee arity (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 ≤ stack.stack.length := by
    constructor
    · rw [selected,frameZero]; exact fixtureStack_nonempty code cfg
    · intro loc call arity callee found
      rw [selected] at call
      have locEq : loc = 65 := by cases call with | left h => cases h | right h => cases h; rfl
      subst loc
      apply calleeFits arity callee
      simpa only [alloc] using found
  obtain ⟨targetPost,targetResult,targetRun,targetResultEq,targetFfi,targetBound⟩ :=
    nativeTailEntry_span wc riscvConfig words 64 entry facts.1 facts.2.1 stack (fixtureWordOracle cfg)
      noRaise noStore codeEq bitmaps init fits clock limit (some (.result (.loc 1 0) [.word word])) wordPost
      (by rw [selected]; exact countdownEntry_shape)
      (by rw [selected]; exact countdownEntry_noInstall)
      (by simpa [nativeTailEntryWord,WordSemStateFiniteExact.callEnv,makeInit] using codeFacts'.1)
      (by rw [selected]; simpa [nativeTailEntryWord,WordSemStateFiniteExact.callEnv,makeInit] using codeFacts'.2)
      (by rw [selected]; exact countdownEntry_convention)
      (by rw [selected]; exact countdownEntry_flat)
      (by rw [selected]; exact wordRun) (by simp) (by simp) (.return [.word word]) frames
      (by rw [selected]; exact wordBound)
  have resultEq : targetResult = some (.result (.loc 1 0)) := by simpa [compileResult] using targetResultEq.symm
  rw [resultEq] at targetRun
  refine ⟨targetPost,targetRun,targetBound,?_⟩
  rw [← targetFfi]
  exact wordFfi
end SteppedFlapjack.Concrete
