import SteppedFlapjack.Concrete.NestedMachine
import SteppedFlapjack.Concrete.Phase7SourceBehaviour

/-! Explicit source-to-RISC-V composition for supported programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordSimpSteps
open Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.StackSteps

open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackToLabSteps

/-- Machine clock as a function of concrete code-derived coefficients and source steps. -/
noncomputable def callPipelineTicks (code : List (Nat × HolProg 64)) (bitmaps : List (BitVec 64))
    (cw tableW progW cf initial sw lf ow ofac ww stackW count : Nat) : Nat :=
  let crep := cw * (1 + (tableW * count + progW) + 2)
  let loop := sw + lf * (initial + cf * (crep + 1))
  let opt := ow + ofac * (2 * loop)
  let word := 6 * opt + 1
  let n := 1 + stackW * (word + ((ww+1) * word + 1))
  948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    bitmaps code (fixtureStackOracle (fixtureCompilerConfig code)) n
/-- Coefficient of the source-step count in the complete pipeline clock. -/
noncomputable def callPipelineFactor (code : List (Nat × HolProg 64)) (bitmaps : List (BitVec 64))
    (cw tableW cf lf ofac ww stackW : Nat) : Nat :=
  let cfg := fixtureCompilerConfig code
  let entry := (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
  let generated := sptFromAList (code1 countdownRiscVBackend.dataConf code)
  let factor := max (costFromFields riscvConfig.addrOffset 0 entry generated bitmaps (fixtureStackOracle cfg))
    (costFromFields riscvConfig.addrOffset 0 entry generated [4] (fixtureStackOracle cfg))
  948 * flattenStepFactor * factor * uniformFactor (width := 64) countdownRiscVBackend.dataConf *
    stackW * (1+(ww+1)) * 6 * ofac * 2 * lf * cf * cw * tableW
set_option maxHeartbeats 2000000 in
/-- If the initial clock is affine in source steps, the complete machine bound
is affine in those steps as well. Both coefficients depend only on the code,
compiler configuration, and the chosen initial-clock slope. -/
theorem callPipelineTicks_affine (code : List (Nat × HolProg 64)) (bitmaps : List (BitVec 64))
    (cw tableW progW cf initialBase initialSlope sw lf ow ofac ww stackW count : Nat) :
    callPipelineTicks code bitmaps cw tableW progW cf (initialBase + initialSlope * count) sw lf ow ofac ww stackW count =
      (callPipelineFactor code bitmaps cw tableW cf lf ofac ww stackW +
        initialSlope * callPipelineFactor code bitmaps 1 1 1 lf ofac ww stackW) * count +
        callPipelineTicks code bitmaps cw tableW progW cf initialBase sw lf ow ofac ww stackW 0 := by
  dsimp only [callPipelineTicks,callPipelineFactor,fixtureStackOracle]
  have h (n : Nat) := stackLabTickLimit_emptyOracle countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bitmaps code (fixtureCompilerConfig code) n
  change ∀ n, stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bitmaps code (fixtureStackOracle (fixtureCompilerConfig code)) n = _ at h
  simp only [h]
  unfold fixtureStackOracle
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- A counted function-only source return reaches the initialized machine with
an explicit tick bound. The concrete checks require the compiler to select no
functions for inlining and the source heap headers to use the compiled bitmap
count. The call-graph capacity check can reject recursion and unresolved calls;
these checks and the fixture layout are restrictions for init-e applicability. -/
theorem countedCalls_initializedMachine {program : Prog (RiscV.Word 64)}
    (supported : ScalarSupported program)     (production : PanSemState (RiscV.Word 64) (FfiState Unit)) (source : PanSemStateFiniteExact 64 Unit)
    [DecidablePred source.memaddrs]
    (sourceFs : List (FunDeclOf 64)) (sourceN sourceClock : Nat)
    (tableSupported : FunctionTableSupported sourceFs)
    (productionInit : production = functionSourceProduction sourceFs sourceN sourceClock)
    (sourceInit : source = functionSourceExact sourceFs sourceN sourceClock)
    (targetCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (entries : List SimpVisits.SimpEntry)
    (sourceEntries : entries = functionsHOL ((sourceFs.map funDeclToHOL).map DeclHOL.function))
    (originalFs : List (FunDeclHOL 64))
    (originalFunctions : originalFs = sourceFs.map funDeclToHOL)
    (originalUnique : ((functionsHOL (originalFs.map DeclHOL.function)).map Prod.fst).Nodup)
    (fs : List (FunDeclHOL 64))
    (simplifiedFs : fs = originalFs.map (fun f => {f with body := panSimpCompileHOL f.body})) (start : MlS)
    (startMain : start = ofString "main")
    (targetTable : targetCode = HolFiniteMapExact.empty.updateList (functionsHOL (fs.map DeclHOL.function)).reverse)
    (mainFound : source.code.lookup start = some ([],progToHOL program,.one))
    (noInline : (functionsHOL ((compileTopExactHOL (fs.map DeclHOL.function) start).filter inlinableHOL)).map Prod.fst = [])
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) (exnContracts : InfoMap Shape) (fuel count : Nat)
    (postLocals postGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (postMemory : BitVec 64 → Option (PanValue (RiscV.Word 64))) (postFfi : FfiState Unit) (value : BitVec 64)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs (countedFunctionsOfCode production.code)
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess production))
      (contracts := some (countedContractsOfCode production.code exnContracts)) =
        some (.returned postLocals postGlobals postMemory postFfi [.word value],count))
    (budget : count ≤ source.clock)
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
    (bitmapLength : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      sourceN = (compileNative riscvConfig false optimized).1.length) :
    let baseState := {source with code := HolFiniteMapExact.empty, structs := [], clock := 0}
    let decls := fs.map DeclHOL.function
    let lowered := compileTopExactHOL decls start
    let renamed := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
    let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
    let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
    let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
    let programs := compileProgDeclsHOLW lowered
    let crep := compileProgExactHOLW panCtxt p
    let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
    let native := compileNative riscvConfig false optimized
    let code := native.2.2.2
    let bitmaps := native.1
    let cfg := fixtureCompilerConfig code
    let initial := concreteDeclCrepState before programs
    let loop := {(concreteDeclLoopState riscvConfig.isa initial programs) with memory := (configuredStack code cfg bitmaps).memory}
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let rows := programs.map (fun row => (row.2.1,row.2.2))
    let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
    let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
    let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
    ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit), ∃ finalMachine finalFfi compilerFinal,
      Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
        (originalFs.map DeclHOL.function) = some (fixtureCodeBytes code,bitmaps,compilerFinal) ∧
      source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word value))),sourceFinal) ∧
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (callPipelineTicks code bitmaps (max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs))
          (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg program)))
          (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
          factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
          (max 1 (stackCodeWeight (sptFromAList code))) count) (configuredMachineState code bitmaps) =
            (.halt .success,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel postFfi sourceFinal.ffi ∧
      semanticsDecls baseState start (originalFs.map DeclHOL.function) = .terminate .success finalFfi.ioEvents := by
  have rawEq : panToWordCompileProgHOL riscvConfig.isa (originalFs.map DeclHOL.function) =
      loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start))) := by
    rw [originalFunctions,simplifiedFs,originalFunctions,startMain]
    exact call_panToWord sourceFs tableSupported
  have sourceGood : pancakeGoodCodeHOL (originalFs.map DeclHOL.function) = true := by
    rw [originalFunctions]
    exact table_good sourceFs tableSupported
  have originalWellFormed : originalFs.all (fun f => f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
      isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true := by
    rw [originalFunctions]
    exact table_wellFormed sourceFs tableSupported
  have unique : ((functionsHOL (fs.map DeclHOL.function)).map Prod.fst).Nodup := by
    rw [simplifiedFs,simp_function_names]
    exact originalUnique
  have sourceCode : source.code = HolFiniteMapExact.empty.updateList entries.reverse := by
    rw [sourceInit,sourceEntries]
    rfl
  have originalEntries : entries = functionsHOL (originalFs.map DeclHOL.function) := by
    rw [sourceEntries,originalFunctions]
  have entryShapes : ∀ entry ∈ entries, ∃ scope, ∃ program : Prog (RiscV.Word 64),
      entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
    rw [sourceEntries]
    exact original_entry_shapes sourceFs tableSupported
  have shapes : ∀ entry ∈ functionsHOL (fs.map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body := by
    rw [simplifiedFs,originalFunctions]
    exact simplified_entry_shapes sourceFs tableSupported
  have codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry := by
    rw [productionInit]
    exact table_code_ranged sourceFs sourceN sourceClock tableSupported
  have codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, CallSupportedIn scope body := by
    rw [productionInit]
    exact table_counted_shapes sourceFs sourceN sourceClock tableSupported
  have ranged : PanSemStateRelExecRanged production := by
    rw [productionInit]
    simp [functionSourceProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words_ : WordLocals production.locals := by
    rw [productionInit]
    exact wordLocals_empty
  have locals : source.locals = HolFiniteMapExact.empty := by rw [sourceInit]; rfl
  have globals : source.globals = HolFiniteMapExact.empty := by rw [sourceInit]; rfl
  have structs : source.structs = [] := by rw [sourceInit]; rfl
  have exceptions : source.eshapes = HolFiniteMapExact.empty := by rw [sourceInit]; rfl
  have topOutside : ¬ source.memaddrs source.topAddr := by
    rw [sourceInit]
    simp [functionSourceExact,sourceTemplateFor,sourceTemplate,ordinaryAddress,heapTop,fixtureHeapEnd,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL source.topAddr := by
    rw [sourceInit]
    change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have rel : PanSemStateRelExec production source.toExact := by
    rw [productionInit,sourceInit]
    exact functionSource_related sourceFs sourceN sourceClock (table_names sourceFs tableSupported)
  have codeRel : PanSimp.CodeRel source.code targetCode := by
    rw [sourceCode, originalEntries, targetTable, simplifiedFs]
    apply source_simp_function_code {source with code := HolFiniteMapExact.empty} originalFs rfl
    · simpa [structs] using originalWellFormed
    · exact originalUnique
  have found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],progToHOL (panSimpProg program),.one) := by
    have h := codeRel.2 start [] (progToHOL program) .one mainFound
    rw [targetTable] at h
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (fs.map DeclHOL.function)).reverse) start = _ at h
    rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,callSupported_panSimp_hol supported.1] at h
    exact h
  let programs := compileProgDeclsHOLW (compileTopExactHOL (fs.map DeclHOL.function) start)
  let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
  let native := compileNative riscvConfig false optimized
  let code := native.2.2.2
  let bitmaps := native.1
  let cfg := fixtureCompilerConfig code
  have memDomain : source.memaddrs = ordinaryAddress := by rw [sourceInit]; rfl
  have sharedDomain : source.shMemaddrs = sharedAddress := by rw [sourceInit]; rfl
  have base : source.baseAddr = heapBase := by rw [sourceInit]; rfl
  have top : source.topAddr = heapTop := by rw [sourceInit]; rfl
  have byteOrder : source.be = false := by rw [sourceInit]; rfl
  have ffi : source.ffi = sourceFfi := by rw [sourceInit]; rfl
  have bitmapLength' : sourceN = bitmaps.length := by
    simpa [bitmaps,native,optimized,raw,programs] using bitmapLength
  have sourceMemory : ∀ a, source.memaddrs a → source.memory a = (sourceTemplateFor bitmaps.length).memory a := by
    rw [sourceInit]
    intro a _
    change HolWordLab.word (initialWordFor sourceN a) = HolWordLab.word (initialWordFor bitmaps.length a)
    rw [bitmapLength']
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have codeEq : (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig raw).2).2.2.2 = code := by
    simp [code,native,optimized,compileWith_eq_compile _ allocator,phase3WordConfig_eq]
  have bitmapEq : (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig raw).2).1 = bitmaps := by
    simp [bitmaps,native,optimized,compileWith_eq_compile _ allocator,phase3WordConfig_eq]
  have safe' : fixtureStackSafe code = true := by
    simpa [code,native,optimized,raw,programs] using safe
  have success' : (fixtureRemoveLabels code).isSome = true := by
    simpa [code,native,optimized,raw,programs] using facts.1
  obtain ⟨compilerFinal,compiled⟩ := fixturePancakeCompiler_outputFor
    (originalFs.map DeclHOL.function) bitmaps raw code rawEq codeEq bitmapEq safe' success'
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := by
    have h := source_nativeGoodCode (originalFs.map DeclHOL.function) originalUnique
    rw [rawEq, ← phase3WordConfig_eq] at h
    simpa [code,native,optimized,raw,programs,compileWith_eq_compile _ allocator] using h
  have bitmapFits' : 0xa0020018 + bitmaps.length*8 ≤ 0xa0410000 := by
    simpa [bitmaps,native,optimized,raw,programs] using bitmapFits
  have fits : 0xa0020018 + bitmaps.length*8 ≤ sourceBase := by simp only [sourceBase]; omega
  obtain ⟨sourceFinal,post,sourceRun,wordRun,_,wordFfi,ffiRel⟩ :=
    countedCalls_initializedWord supported.1 production source rel ranged words_ supported.2 codeRanged codeShape
      targetCode codeRel entries sourceCode entryShapes fs start targetTable found mainFound locals globals structs
      exceptions unique shapes noInline topOutside aligned context primitive handler exnContracts fuel count
      postLocals postGlobals postMemory postFfi value run budget phase3WordConfig code cfg bitmaps fits good
      memDomain sharedDomain base top byteOrder ffi
      sourceMemory
  let decls := fs.map DeclHOL.function
  let lowered := compileTopExactHOL decls start
  let renamed : PanSemStateFiniteExact 64 Unit := {source with code := fpermCodeHOL start (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let initial := concreteDeclCrepState before programs
  let loop := {(concreteDeclLoopState riscvConfig.isa initial programs) with memory := (configuredStack code cfg bitmaps).memory}
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
  let crep := compileProgExactHOLW panCtxt p
  let crepLimit := max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs) *
    (1 + (SimpVisits.simpTableFactor entries * count + SimpVisits.hw (progToHOL (panSimpProg program))) + 2)
  let rows := programs.map (fun row => (row.2.1,row.2.2))
  let extra := callClockFactor ctxt rows initial.clock crep * (crepLimit+1)
  let factor := max (callSyntaxCost ctxt crep) (loopCodeWeight loop.code+2)
  let loopLimit := callSyntaxCost ctxt crep + factor * (initial.clock+extra)
  let opt := optimiseHOL (compileHOLExact ctxt .ln crep)
  let optFactor := max (loopVisitWeight opt) (loopCodeWeight loop.code+2)
  let optLimit := loopVisitWeight opt + optFactor * (2*loopLimit)
  have machine := functionOnly_initialized_machine fs start (progToHOL (panSimpProg program)) found noInline
    (originalFs.map DeclHOL.function) originalUnique rawEq optLimit value sourceGood bitmapFits safe facts capacity post
    (by simpa [programs,raw,optimized,native,code,bitmaps,cfg,compileWith_eq_compile _ allocator,firstLoopName] using wordRun)
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := machine
  have finalEvents : finalFfi.ioEvents = sourceFinal.ffi.ioEvents := events.trans (congrArg (fun f => f.ioEvents) wordFfi)
  have foundOriginal : (functionsHOL (originalFs.map DeclHOL.function)).lookup start = some ([],progToHOL program,.one) := by
    have h := mainFound
    rw [sourceCode,originalEntries] at h
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (originalFs.map DeclHOL.function)).reverse) start = _ at h
    rwa [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at h
  let baseState : PanSemStateFiniteExact 64 Unit := {source with code := HolFiniteMapExact.empty, structs := [], clock := 0}
  have sourceRun' : (let declared := {baseState with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (originalFs.map DeclHOL.function)).reverse)}
      ({declared with clock := source.clock} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState (progToHOL program) =
        (some (.returned (.val (.word value))),sourceFinal)) := by
    have codeEq : HolFiniteMapExact.empty.updateList (functionsHOL (originalFs.map DeclHOL.function)).reverse = source.code := by
      rw [← originalEntries, ← sourceCode]
    dsimp only [baseState]
    rw [codeEq, ← structs]
    exact sourceRun
  have semantics := functionOnly_body_semantics baseState start originalFs (progToHOL program)
    originalWellFormed originalUnique rfl (by simpa [baseState] using locals) foundOriginal source.clock sourceFinal value sourceRun'
  exact ⟨sourceFinal,finalMachine,finalFfi,compilerFinal,compiled,sourceRun,machineRun,finalEvents,ffiRel,by simpa [finalEvents] using semantics⟩

end SteppedFlapjack.Concrete
