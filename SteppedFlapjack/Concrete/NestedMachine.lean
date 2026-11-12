import SteppedFlapjack.Concrete.NestedLoopRun
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.WordToStackSteps.StartRiscV
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps

/-- All generated Loop function locations follow the reserved runtime stubs. -/
theorem compiledLoop_locations_ge (arch : AsmArchitecture) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (location : Nat) (member : location ∈ (compileProgHOLExact arch programs).map Prod.fst) : firstLoopName ≤ location := by
  obtain ⟨entry,member,heq⟩ := List.mem_map.mp member
  subst location
  obtain ⟨i,hi,entryEq⟩ := List.mem_iff_getElem.mp member
  simp only [compileProgHOLExact,List.length_zipWith,List.length_map,List.length_range,Nat.min_self] at hi
  simp only [compileProgHOLExact,List.getElem_zipWith,List.getElem_map,List.getElem_range] at entryEq
  rw [← entryEq]
  omega
/-- Generated Word function locations cannot collide with the native runtime stubs. -/
theorem compiledWord_noStubs (arch : AsmArchitecture) (programs : List (MlS × List Nat × CrepProgHOL 64)) :
    let words := loopToWordCompileHOL (compileProgHOLExact arch programs)
    raiseStubLocation ∉ words.map Prod.fst ∧ storeConstsStubLocation ∉ words.map Prod.fst := by
  have names : (loopToWordCompileHOL (compileProgHOLExact arch programs)).map Prod.fst =
      (compileProgHOLExact arch programs).map Prod.fst := by
    simp [loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def]
  change raiseStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch programs)).map Prod.fst ∧
    storeConstsStubLocation ∉ (loopToWordCompileHOL (compileProgHOLExact arch programs)).map Prod.fst
  rw [names]
  constructor <;> intro member
  · have h := compiledLoop_locations_ge arch programs raiseStubLocation member
    simp [raiseStubLocation,firstLoopName,wordNumStubs,stackNumStubs] at h
  · have h := compiledLoop_locations_ge arch programs storeConstsStubLocation member
    simp [storeConstsStubLocation,firstLoopName,wordNumStubs,stackNumStubs] at h

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
/-- Native frame-size table computed from the actual optimized functions. -/
def nestedFrameSizes : Spt Nat :=
  sptMapi (fun _ (argc,body) =>
    (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
    (sptFromAList nestedOptimizedWords)

theorem nested_panToWord :
    panToWordCompileProgHOL riscvConfig.isa (nestedCallDeclarations.map declToHOL) = nestedRawWords := by
  have funcs : nestedHOLFunctions = nestedSourceFunctions.map funDeclToHOL := by
    simp [nestedHOLFunctions,nestedSourceFunctions,nestedCallEntry,funDeclToHOL,progToHOL,expToHOL,shapeToHOL]
  have fixed : nestedHOLFunctions.map (fun f => {f with body := panSimpCompileHOL f.body}) = nestedHOLFunctions := by
    simp [nestedHOLFunctions,nestedCallEntry,progToHOL,expToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL]
  have result := call_panToWord nestedSourceFunctions nested_table_supported
  rw [← funcs,fixed,nestedHOLDeclarations] at result
  exact result

/-- The actual source compiler output satisfies the Stack code contract. -/
theorem nested_nativeGoodCode : StackToLab.Proofs.GoodCode.goodCode 24
    (compileNative riscvConfig false nestedOptimizedWords).2.2.2 := by
  have unique : ((functionsHOL (nestedCallDeclarations.map declToHOL)).map Prod.fst).Nodup := by
    simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]
    decide
  have good := source_nativeGoodCode (nestedCallDeclarations.map declToHOL) unique
  rw [nested_panToWord] at good
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simpa [nestedOptimizedWords,nestedRawWords,compileWith_eq_compile _ allocator,phase3WordConfig_eq] using good

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- A generated, initialized Word return reaches RISC-V at a concrete bound. -/
theorem functionOnly_configured_machine
    (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (rawEq : panToWordCompileProgHOL riscvConfig.isa pan =
      loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))))
    (cfg : LabToTarget.Config) (limit : Nat) (value : BitVec 64)
    (fits : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let bitmaps := (compileNative riscvConfig false optimized).1
      0xa0020018 + bitmaps.length*8 ≤ sourceBase)
    (capacity : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
      let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
      let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
        (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
      optionLe (optionMap₂ max (some (max 1 (1+frame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172))
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit)
    (run : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let native := compileNative riscvConfig false optimized
      let code := native.2.2.2
      let bs := native.1
      WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
        {(configuredWord code optimized cfg bs) with clock := 6*limit+1} =
          (some (.result (.loc 1 0) [.word value]),wordPost))
    (filtered : LabSem.State 64 LabToTarget.Config Unit)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget)
    (link : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let native := compileNative riscvConfig false optimized
      LabToTargetSteps.LabExecutionLink filtered (configuredTargetLab native.2.2.2 cfg native.1 machine))
    (tie : LabToTarget.oracleTie mc machine filtered)
    (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
    let native := compileNative riscvConfig false optimized
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) ^ (6*limit+2)
    let n := 1 + max 1 (stackCodeWeight (sptFromAList native.2.2.2)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc sourceFfi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          native.1 native.2.2.2 (fixtureStackOracle cfg) n) machine =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = wordPost.ffi.ioEvents := by
  let programs := compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)
  let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let words := (compile phase3WordConfig riscvConfig raw).2
  let native := compileNative riscvConfig false words
  let code := native.2.2.2
  let bs := native.1
  let tail := bs.drop 1
  let entry := ((sptLookup 64 (sptFromAList words)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList words)
  let source := {(configuredWord code words cfg bs) with clock := 6*limit+1}
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have bsHeader : bs = 4 :: tail := nativeBitmaps_header words
  have fits' : 0xa0020018 + bs.length*8 ≤ sourceBase := by
    simpa [bs,native,words,raw,programs,compileWith_eq_compile _ allocator] using fits
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := by
    have g := source_nativeGoodCode pan unique
    rw [rawEq, ← phase3WordConfig_eq] at g
    exact g
  have entries := functionOnly_initializedEntry fs start body found noInline phase3WordConfig code cfg bs
  have entryLookup : sptLookup 64 (configuredWord code words cfg bs).code = some (1,entry) := by
    simpa [programs,raw,words,entry] using entries.1
  have frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame := by
    simpa [programs,raw,words,entry,frame] using entries.2
  have noStubs := compiledWord_noStubs riscvConfig.isa programs
  have noRaise : raiseStubLocation ∉ raw.map Prod.fst := noStubs.1
  have noStore : storeConstsStubLocation ∉ raw.map Prod.fst := noStubs.2
  have fields := configuredStack_code_and_bitmaps code cfg bs fits' good
  have initOk := configuredStack_nativeInitOk code cfg tail (by simpa [bsHeader] using fits') good
  have related := wholeWordStack_initStateRel phase3WordConfig riscvConfig raw
    (configuredStack code cfg bs) (configuredWordOracle cfg bs) noRaise noStore
    (by rw [fields.1]) (by rw [fields.2]) (by simpa [bsHeader] using initOk)
  have clockRelated := stateRel_setClocks riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    0 0 _ _ [] 0 (6*limit+1) related
  have targetSafe := wholeCompile_targetSafety phase3WordConfig riscvConfig raw (loopToWord_programSafety _)
  have safe : safeWordCode source := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,safeWordCode,words] using
      ⟨targetSafe.2.1,targetSafe.1⟩
  have noAlloc : WordProps.noAllocCode source.code := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,words] using targetSafe.2.2
  have args : WordSemStateFiniteExact.getVars [0] source = some [(.loc 1 0)] := by
    simp [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,sptLookup]
  have loc : BvlToBvi.initGlobalsLocation = 64 := by decide
  have capacity' : optionLe (optionMap₂ max (some (max 1 (1+frame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList words))))
      (some (configuredStack code cfg bs).stack.length) := by
    rw [configuredStack_stackLength code cfg bs fits' good]
    simpa [frame,entry,frames,words,raw,programs,compileWith_eq_compile _ allocator] using capacity
  have machineCapacity : let t := callEnv [(.loc 1 0 : WordLocW 64)] (some frame) (decClock source)
      optionLe (optionMap₂ max t.stackMax (optionMap₂ (· + ·) (wordSemStackSize t.stack)
        (fullCallGraphDepth t.stackSize 64 t.code))) (some t.stackLimit) := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,
      WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,wordSemStackSize,wordSemOptionMax,
      wordSemOptionAdd,frames,words,raw] using capacity'
  have hA := configuredTargetLab_assumptions code cfg bs machine fits' good
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := wordStart_riscv_explicit riscvConfig
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownRiscVBackend.stackConf
    countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code (configuredTargetLab code cfg bs machine) filtered
    fixtureSavedRegs 0 (fixtureStackOracle cfg) (by intro i; rfl) hA source wordPost
    (some (.result (.loc 1 0) [.word value])) .success (by rw [configuredTargetLab_stack]; simpa [source,configuredWord] using clockRelated)
    safe noAlloc (by simpa [source,bs,native,code,words,raw,programs,compileWith_eq_compile _ allocator,loc] using run)
    (by simp) (by simp) entry frame (.loc 1 0) (by simpa [source,loc] using entryLookup)
    (by simpa [source,loc] using frameLookup) args (by simp [source]) machineCapacity (by rfl)
    pc mc labCode labs asm machine hmc (by simpa [bs,native,code,words,raw,programs,compileWith_eq_compile _ allocator] using link) tie rel
  have allowanceEq : callTableBudget (.call none (some 64) [0] none) source =
      (max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable
        phase3WordConfig riscvConfig raw).2)) + 1) ^ (6*limit+2) := by
    rw [compileWith_eq_compile _ allocator]
    simp [callTableBudget,fixedTableBudget,wordControlWeight,source,configuredWord,
      Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,words]
  simp only [loc] at machineRun
  rw [allowanceEq] at machineRun
  refine ⟨finalMachine,finalFfi,?_,events⟩
  simpa [configuredTargetLab_shape,configuredLab,fixtureLab,source,words,raw,bs,code,native,programs,compileWith_eq_compile _ allocator] using machineRun

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem functionOnly_initialized_machine
    (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (pan : List (DeclHOL 64)) (unique : ((functionsHOL pan).map Prod.fst).Nodup)
    (rawEq : panToWordCompileProgHOL riscvConfig.isa pan =
      loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))))
    (limit : Nat) (value : BitVec 64)
    (sourceGood : pancakeGoodCodeHOL pan = true)
    (bitmapFits : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let bitmaps := (compileNative riscvConfig false optimized).1
      0xa0020018 + bitmaps.length*8 ≤ 0xa0410000)
    (safe : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      fixtureStackSafe (compileNative riscvConfig false optimized).2.2.2 = true)
    (facts : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let code := (compileNative riscvConfig false optimized).2.2.2
      (fixtureRemoveLabels code).isSome = true ∧ (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0)
    (capacity : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
      let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
      let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
        (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
      optionLe (optionMap₂ max (some (max 1 (1+frame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172))
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit)
    (run : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let native := compileNative riscvConfig false optimized
      let code := native.2.2.2
      let bs := native.1
      let cfg := fixtureCompilerConfig code
      WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
        {(configuredWord code optimized cfg bs) with clock := 6*limit+1} =
          (some (.result (.loc 1 0) [.word value]),wordPost))
 :
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
    let native := compileNative riscvConfig false optimized
    let code := native.2.2.2
    let bitmaps := native.1
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) ^ (6*limit+2)
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bitmaps code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bitmaps) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = wordPost.ffi.ioEvents := by
  let programs := compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)
  let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
  let native := compileNative riscvConfig false optimized
  let code := native.2.2.2
  let bitmaps := native.1
  let cfg := fixtureCompilerConfig code
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := by
    have h := source_nativeGoodCode pan unique
    rw [rawEq, ← phase3WordConfig_eq] at h
    simpa [code,native,optimized,raw,programs,compileWith_eq_compile _ allocator] using h
  have labGood : LabToTarget.goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab code cfg).code) := by
    have h := source_labGoodCode pan raw rawEq sourceGood unique
    simpa [fixtureLab,code,cfg,native,optimized,raw,programs,compileWith_eq_compile _ allocator,phase3WordConfig_eq] using h
  have bitmapFits' : 0xa0020018 + bitmaps.length*8 ≤ 0xa0410000 := by
    simpa [bitmaps,native,optimized,raw,programs] using bitmapFits
  have fits : 0xa0020018 + bitmaps.length*8 ≤ sourceBase := by simp only [sourceBase]; omega
  have safe' : fixtureStackSafe code = true := by simpa [code,native,optimized,raw,programs] using safe
  have facts' : (fixtureRemoveLabels code).isSome = true ∧ (fixtureCodeBytes code).length ≤ 0xecc ∧
      (fixtureCodeBytes code).length % 4 = 0 := by simpa [code,native,optimized,raw,programs] using facts
  have removed : LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (configuredLab code cfg bitmaps).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := fixtureRemoveLabels_eq code facts'.1
  have guards := configuredMachine_allGuards code bitmaps bitmapFits' labGood safe' facts'
  obtain ⟨filtered,link,tie,rel,buffer⟩ := configuredMachine_relations code cfg bitmaps bitmapFits'
    (fixtureCompiled code).1 (fixtureCompiled code).2 good removed guards
  have result := functionOnly_configured_machine fs start body found noInline pan unique rawEq cfg limit value fits capacity
    wordPost (by simpa [programs,raw,optimized,native,code,bitmaps,cfg] using run)
    filtered (fixtureCodeStart code) (fixtureMachineConfig (fixtureCodeStart code))
    (fixtureCompiled code).1 (fixtureCompiled code).2 (configuredMachineAsm code bitmaps)
    (configuredMachineState code bitmaps) rfl
    (by simpa [programs,raw,optimized,native,code,bitmaps] using link) tie rel
  simp only [buffer,fixtureLabMachineFactor code facts'.2.1] at result
  exact result


end SteppedFlapjack.Concrete
