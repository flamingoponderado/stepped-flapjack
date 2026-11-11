import SteppedFlapjack.Concrete.NestedWordSpan
import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.WordToStackSteps.StartRiscV
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps

/-- Executable Word table and entry frame for the nested-call witness. -/
def nestedRawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
def nestedOptimizedWords := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig nestedRawWords).2
def nestedEntry : WordLangProgHOL (BitVec 64) :=
  ((sptLookup 64 (sptFromAList nestedOptimizedWords)).getD (1,.skip)).2
def nestedEntryFrame : Nat :=
  (compileProgNative riscvConfig false nestedEntry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1

/-- Native Stack code and bitmaps computed from the actual optimized table. -/
def nestedNative := compileNative riscvConfig false nestedOptimizedWords
def nestedCode : List (Nat × HolProg 64) := nestedNative.2.2.2
def nestedBitmaps : List (BitVec 64) := nestedNative.1
def nestedBitmapTail : List (BitVec 64) := nestedBitmaps.drop 1

theorem nestedBitmaps_header : nestedBitmaps = 4 :: nestedBitmapTail := by
  rcases hn : compileNative riscvConfig false nestedOptimizedWords with ⟨bs,config,rest⟩
  have h := compileWordToStackBitmaps riscvConfig nestedOptimizedWords bs config rest hn
  have bsEq : nestedBitmaps = bs := by simp [nestedBitmaps,nestedNative,hn]
  cases bs with
  | nil => simp at h
  | cons head tail =>
    have eq : head = 4 := h.1.symm
    subst head
    simp [nestedBitmapTail,bsEq]

/-- Native frame-size table computed from the actual optimized functions. -/
def nestedFrameSizes : Spt Nat :=
  sptMapi (fun _ (argc,body) =>
    (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
    (sptFromAList nestedOptimizedWords)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem nested_simp_declarations :
    panSimpDeclsHOL (nestedCallDeclarations.map declToHOL) = nestedCallDeclarations.map declToHOL := by
  simp [nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem nested_struct_declarations :
    Pancake.PanStructs.CompileShapeExact.compileTopExact (nestedCallDeclarations.map declToHOL) =
      nestedCallDeclarations.map declToHOL := by
  simp [nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    Pancake.PanStructs.CompileShapeExact.compileTopExact,Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Pancake.PanStructs.CompileShapeExact.compileProgExact,Pancake.PanStructs.CompileShapeExact.compileShapeExact,
    Pancake.PanStructs.CompileShapeExact.compileExpExact,Pancake.PanStructs.CompileShapeExact.compileExpsExact]

theorem nested_panToWord :
    panToWordCompileProgHOL riscvConfig.isa (nestedCallDeclarations.map declToHOL) = nestedRawWords := by
  simp only [panToWordCompileProgHOL,nested_simp_declarations,nested_struct_declarations]
  rfl

/-- The actual source compiler output satisfies the Stack code contract. -/
theorem nested_nativeGoodCode : StackToLab.Proofs.GoodCode.goodCode 24
    (compileNative riscvConfig false nestedOptimizedWords).2.2.2 := by
  let pan := nestedCallDeclarations.map declToHOL
  let w := compile countdownRiscVBackend.wordToWordConf riscvConfig nestedRawWords
  let st := compileNative riscvConfig false w.2
  have h := Flapjack.Pancake.Proofs.PanToTarget.word_to_stack_good_code_lemma countdownRiscVBackend countdownMachineConfig
    pan w.1 w.2 st.1 st.2.1 st.2.2.1 st.2.2.2
  have hw : compile countdownRiscVBackend.wordToWordConf countdownMachineConfig.target.config
      (panToWordCompileProgHOL countdownMachineConfig.target.config.isa pan) = (w.1,w.2) := by
    change compile countdownRiscVBackend.wordToWordConf riscvConfig (panToWordCompileProgHOL riscvConfig.isa pan) = _
    rw [show panToWordCompileProgHOL riscvConfig.isa pan = nestedRawWords from nested_panToWord]
  have hs : compileNative countdownMachineConfig.target.config false w.2 = (st.1,st.2.1,st.2.2.1,st.2.2.2) := by rfl
  have hn : ((functionsHOL pan).map Prod.fst).Nodup := by
    simp [pan,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]
    decide
  have good := h ⟨hw,by decide,hs,by decide,hn⟩
  have reg : countdownMachineConfig.target.config.regCount -
      (countdownMachineConfig.target.config.avoidRegs.length + 3) = 24 := by decide
  rw [reg] at good
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simpa [nestedOptimizedWords,compileWith_eq_compile _ allocator,phase3WordConfig_eq,w,st] using good

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The source-derived nested-call code reaches RISC-V at an explicit tick bound
when its concrete memory-capacity and machine-initialization checks hold. -/
theorem nested_configured_machine (cfg : LabToTarget.Config)
    (fits : 0xa0020018 + nestedBitmaps.length*8 ≤ sourceBase)
    (capacity : optionLe
      (optionMap₂ max (some (max 1 (1+nestedEntryFrame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth nestedFrameSizes 64 (sptFromAList nestedOptimizedWords))))
      (some 2097172))
    (filtered : LabSem.State 64 LabToTarget.Config Unit)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget)
    (link : LabToTargetSteps.LabExecutionLink filtered (configuredTargetLab nestedCode cfg nestedBitmaps machine))
    (tie : LabToTarget.oracleTie mc machine filtered)
    (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let rawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig rawWords).2
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) ^ (6*nestedOptimizedLoopBound+2)
    let n := 1 + max 1 (stackCodeWeight (sptFromAList nestedCode)) * (6*nestedOptimizedLoopBound+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc sourceFfi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          nestedBitmaps nestedCode (fixtureStackOracle cfg) n) machine =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplateFor nestedBitmaps.length with clock := 0} (ofString "main")
        (nestedCallDeclarations.map declToHOL) = .terminate .success finalFfi.ioEvents := by
  let code := nestedCode
  let tail := nestedBitmapTail
  let rawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
  let words := (compile phase3WordConfig riscvConfig rawWords).2
  let bs := (4 :: tail : List (BitVec 64))
  have bsEq : bs = nestedBitmaps := nestedBitmaps_header.symm
  have fits' : 0xa0020018 + bs.length*8 ≤ sourceBase := by rw [bsEq]; exact fits
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := nested_nativeGoodCode
  let source := {(configuredWord code words cfg bs) with clock := 6*nestedOptimizedLoopBound+1}
  let frame := nestedEntryFrame
  let entry := nestedEntry
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have optEq : nestedOptimizedWords = words := by
    simp [nestedOptimizedWords,nestedRawWords,words,rawWords,compileWith_eq_compile _ allocator]
  have nativeCode : code = (compileNative riscvConfig false words).2.2.2 := by
    simp [code,nestedCode,nestedNative,optEq]
  have bitmapPrefix : (compileNative riscvConfig false words).1.IsPrefix bs := by
    have eq : (compileNative riscvConfig false words).1 = bs := by
      simpa [nestedBitmaps,nestedNative,optEq] using bsEq.symm
    rw [eq]
  have member : (64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64) ∈ rawWords := by
    simp [rawWords,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have nodup : (rawWords.map Prod.fst).Nodup := by
    simp [rawWords,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have outputLookup := (wholeCompile_entry_lookups phase3WordConfig riscvConfig rawWords 64 1 _ member nodup).2
  have executableLookup : sptLookup 64 (sptFromAList nestedOptimizedWords) =
      some (1,(fullCompileSingle riscvConfig.twoRegArith (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
        phase3WordConfig.regAlg riscvConfig ((64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64),
          entryColour phase3WordConfig rawWords 64)).2.2) := by
    simpa [nestedOptimizedWords,nestedRawWords,rawWords,compileWith_eq_compile _ allocator] using outputLookup
  have entryValue : entry = (fullCompileSingle riscvConfig.twoRegArith
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) phase3WordConfig.regAlg riscvConfig
      ((64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64),entryColour phase3WordConfig rawWords 64)).2.2 := by
    simp [entry,nestedEntry,executableLookup]
  have optLookup : sptLookup 64 (sptFromAList words) = some (1,entry) := by
    rw [entryValue]
    simpa [words,rawWords,nestedOptimizedWords,nestedRawWords,compileWith_eq_compile _ allocator] using executableLookup
  have entryLookup : sptLookup 64 (configuredWord code words cfg bs).code = some (1,entry) := by
    simpa [configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit] using optLookup
  have frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame := by
    simp [configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit,sptLookupMapi,optLookup,
      frame,nestedEntryFrame,entry]
  obtain ⟨post,run,ffi,_⟩ := nested_configured_optimized_start code cfg bs fits' good frame frameLookup
  have noRaise : raiseStubLocation ∉ rawWords.map Prod.fst := by
    simp [rawWords,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL,raiseStubLocation,wordNumStubs,stackNumStubs]
  have noStore : storeConstsStubLocation ∉ rawWords.map Prod.fst := by
    simp [rawWords,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL,storeConstsStubLocation,wordNumStubs,stackNumStubs]
  have fields := configuredStack_code_and_bitmaps code cfg bs fits' good
  have initOk := configuredStack_nativeInitOk code cfg tail fits' good
  have related := wholeWordStack_initStateRel phase3WordConfig riscvConfig rawWords
    (configuredStack code cfg bs) (configuredWordOracle cfg bs) noRaise noStore
    (by rw [fields.1,nativeCode]) (by rw [fields.2]; exact bitmapPrefix) initOk
  have clockRelated := stateRel_setClocks riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    0 0 _ _ [] 0 (6*nestedOptimizedLoopBound+1) related
  have targetSafe := wholeCompile_targetSafety phase3WordConfig riscvConfig rawWords (loopToWord_programSafety _)
  have safe : safeWordCode source := by
    simpa [source,configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit,safeWordCode,words] using
      ⟨targetSafe.2.1,targetSafe.1⟩
  have noAlloc : WordProps.noAllocCode source.code := by
    simpa [source,configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit,words] using targetSafe.2.2
  have args : WordSemStateFiniteExact.getVars [0] source = some [(.loc 1 0)] := by
    simp [source,configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,sptLookup]
  have loc : BvlToBvi.initGlobalsLocation = 64 := by decide
  have capacity' : optionLe
      (optionMap₂ max (some (max 1 (1+nestedEntryFrame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth nestedFrameSizes 64 (sptFromAList nestedOptimizedWords))))
      (some (configuredStack code cfg bs).stack.length) := by
    rw [configuredStack_stackLength code cfg bs fits' good]
    exact capacity
  have machineCapacity : let t := callEnv [(.loc 1 0 : WordLocW 64)] (some frame) (decClock source)
      optionLe (optionMap₂ max t.stackMax (optionMap₂ (· + ·) (wordSemStackSize t.stack)
        (fullCallGraphDepth t.stackSize 64 t.code))) (some t.stackLimit) := by
    simpa [source,configuredWord,Compiler.Backend.WordToStack.Native.Initialization.makeInit,
      WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,wordSemStackSize,wordSemOptionMax,
      wordSemOptionAdd,nestedFrameSizes,nestedOptimizedWords,nestedRawWords,words,rawWords,bs,frame,
      compileWith_eq_compile _ allocator] using capacity'
  have hA := configuredTargetLab_assumptions code cfg bs machine fits' good
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := wordStart_riscv_explicit riscvConfig
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownRiscVBackend.stackConf
    countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code (configuredTargetLab code cfg bs machine) filtered
    fixtureSavedRegs 0 (fixtureStackOracle cfg) (by intro i; rfl) hA source post
    (some (.result (.loc 1 0) [.word 7])) .success (by rw [configuredTargetLab_stack]; simpa [source,configuredWord] using clockRelated)
    safe noAlloc run (by simp) (by simp) entry frame (.loc 1 0) (by simpa [source,loc] using entryLookup)
    (by simpa [source,loc] using frameLookup) args (by simp [source]) machineCapacity (by rfl)
    pc mc labCode labs asm machine hmc (by simpa [code,bsEq] using link) tie rel
  have allowanceEq : callTableBudget (.call none (some 64) [0] none) source =
      (max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable
        phase3WordConfig riscvConfig rawWords).2)) + 1) ^ (6*nestedOptimizedLoopBound+2) := by
    rw [compileWith_eq_compile _ allocator]
    simp [callTableBudget,fixedTableBudget,wordControlWeight,source,configuredWord,
      Compiler.Backend.WordToStack.Native.Initialization.makeInit,words]
  simp only [loc] at machineRun
  rw [allowanceEq] at machineRun
  have outputEvents : finalFfi.ioEvents = sourceFfi.ioEvents := by rw [events,ffi]
  refine ⟨finalMachine,finalFfi,?_,outputEvents,?_⟩
  · simpa [configuredTargetLab_shape,configuredLab,fixtureLab,source,words,rawWords,bs,tail,code,← nestedBitmaps_header] using machineRun
  · simpa [outputEvents,sourceFfi] using nestedCall_source_semantics nestedBitmaps.length

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The source compiler provides the nested witness's Lab good-code fact. -/
theorem nested_labGoodCode (cfg : LabToTarget.Config) :
    LabToTarget.goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab nestedCode cfg).code) := by
  have nodup : ((functionsHOL (nestedCallDeclarations.map declToHOL)).map Prod.fst).Nodup := by
    simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]
    decide
  have sourceGood : pancakeGoodCodeHOL (nestedCallDeclarations.map declToHOL) = true := by
    decide +kernel
  have good := source_labGoodCode (nestedCallDeclarations.map declToHOL) nestedRawWords nested_panToWord sourceGood nodup
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simpa [fixtureLab,nestedCode,nestedNative,nestedOptimizedWords,
    compileWith_eq_compile _ allocator,phase3WordConfig_eq] using good


end SteppedFlapjack.Concrete
