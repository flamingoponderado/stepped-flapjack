import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.FixtureMachineResults
import SteppedFlapjack.Concrete.BranchingFrames
import SteppedFlapjack.Concrete.CountdownOptimized
import SteppedFlapjack.Concrete.CountdownLabBounds
import SteppedFlapjack.Concrete.WitnessWeights

/-! Concrete instances of the supported source-to-machine theorem. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordToStackSteps

private def witnessContext : PanValueFfiContext (RiscV.Word 64) := riscv64PanValueFfiContext (fun _ => false)
private def witnessPrimitive : PanPrimitiveHandler (RiscV.Word 64) := fun _ _ => none
private def witnessHandler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit := fun _ _ _ _ _ _ _ => none

def comparisonSourceFunctions : List (FunDeclOf 64) := [⟨"main",false,false,[],branching,.one⟩]
private def comparisonProduction := functionSourceProduction comparisonSourceFunctions 1 6
private theorem comparison_sourceRun (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler comparisonProduction.structs (countedFunctionsOfCode comparisonProduction.code)
      comparisonProduction.baseAddress comparisonProduction.topAddress panSemBitVec64BytesInWord 2 comparisonProduction.locals comparisonProduction.globals comparisonProduction.memory comparisonProduction.ffi branching
      (memoryAccess := some (panSemBitVec64MemoryAccess comparisonProduction))
      (contracts := some (countedContractsOfCode comparisonProduction.code [])) =
      some (.returned comparisonProduction.locals comparisonProduction.globals comparisonProduction.memory comparisonProduction.ffi [.word 7],6) := by
  rw [supported_calls_irrel context primitive handler comparisonProduction.structs
    (countedFunctionsOfCode comparisonProduction.code) [] comparisonProduction.baseAddress comparisonProduction.topAddress
    panSemBitVec64BytesInWord 2 (some (panSemBitVec64MemoryAccess comparisonProduction))
    (some (countedContractsOfCode comparisonProduction.code [])) [] branching branching_supported.1]
  simpa [comparisonProduction,functionSourceProduction,sourceProduction,initialWordFor_one,
    executableState,singleEntrySourceProduction,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,
    panSemBitVec64WordModel,panSemWordModel,RiscV.panRiscVMemoryModel] using branching_run context primitive handler

open Flapjack.Basis.Pure.MlString
def comparisonHOLFunctions := comparisonSourceFunctions.map funDeclToHOL
def comparisonSimpFunctions := comparisonHOLFunctions.map (fun f => {f with body := panSimpCompileHOL f.body})
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem comparison_noInline : (functionsHOL ((compileTopExactHOL (comparisonSimpFunctions.map DeclHOL.function) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  simp [comparisonSimpFunctions,comparisonHOLFunctions,comparisonSourceFunctions,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,branching,compileTopExactHOL,functionsHOL,
    compileTopFunctionLookup_eq_lookup,List.lookup,resortDeclsHOL,newMainNameHOL,isNameHOL,isDeclHOL,
    isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,
    compileExpExactHOL,inlinableHOL,functionsHOL]
private theorem comparison_simpDeclarations : comparisonSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg branching)) := by
  rw [branching_simp_program]
  simp [comparisonSimpFunctions,comparisonHOLFunctions,comparisonSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,branching]
private theorem comparison_nativeCode : (supportedNative branching).2.2.2 = comparisonNativeCode := by
  have words : supportedWordPrograms branching = comparisonWordPrograms := by
    unfold supportedWordPrograms
    rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,comparisonNativeCode]
def comparisonSource := functionSourceExact comparisonSourceFunctions 1 6
private instance : DecidablePred comparisonSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
noncomputable def comparisonTicks : Nat :=
  let entries := functionsHOL (comparisonHOLFunctions.map DeclHOL.function)
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (comparisonSimpFunctions.map DeclHOL.function)).reverse
  let decls := comparisonSimpFunctions.map DeclHOL.function
  let lowered := compileTopExactHOL decls (ofString "main")
  let renamed := {comparisonSource with code := fpermCodeHOL (ofString "main") (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
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
  callPipelineTicks code bitmaps (max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs))
    (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg branching)))
    (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
    factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
    (max 1 (stackCodeWeight (sptFromAList code))) 6
def comparisonOptimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (comparisonSimpFunctions.map DeclHOL.function) (ofString "main")))))).2
def comparisonNative := compileNative riscvConfig false comparisonOptimized
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The comparison program reaches the machine through the call-aware theorem. -/
theorem comparisonFixture_machine : ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (comparisonHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes comparisonNative.2.2.2,comparisonNative.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart comparisonNative.2.2.2)) sourceFfi
      comparisonTicks (configuredMachineState comparisonNative.2.2.2 comparisonNative.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (comparisonHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  have shape : Supported branching := branching_supported.toSupported
  have table : FunctionTableSupported comparisonSourceFunctions := by
    intro f hf
    simp only [comparisonSourceFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
    subst f
    refine ⟨?_,shape.1,?_,rfl⟩
    · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,shape.2]
    · simp
  have unique : ((functionsHOL (comparisonHOLFunctions.map DeclHOL.function)).map Prod.fst).Nodup := by
    simp [comparisonHOLFunctions,comparisonSourceFunctions,funDeclToHOL,functionsHOL]
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (comparisonSimpFunctions.map DeclHOL.function)).reverse
  have span := countedCalls_initializedMachine shape comparisonProduction comparisonSource comparisonSourceFunctions 1 6 table rfl rfl targetCode
    (functionsHOL (comparisonHOLFunctions.map DeclHOL.function)) (by rfl)
    comparisonHOLFunctions rfl unique comparisonSimpFunctions rfl (ofString "main") rfl rfl
    (by simp [comparisonSource,functionSourceExact,comparisonSourceFunctions,funDeclToHOL,shapeToHOL,functionsHOL,
      HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,ofString])
    comparison_noInline (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 2 6
    _ _ _ _ 7 (comparison_sourceRun _ _ _) (by rfl)
    (by
      rw [comparison_simpDeclarations]
      change 0xa0020018 + (supportedNative branching).1.length*8 ≤ 0xa0410000
      rw [supported_native_bitmap branching branching_supported]
      decide)
    (by
      rw [comparison_simpDeclarations]
      change fixtureStackSafe (supportedNative branching).2.2.2 = true
      rw [comparison_nativeCode]
      exact comparison_stackSafe)
    (by
      rw [comparison_simpDeclarations]
      change (fixtureRemoveLabels (supportedNative branching).2.2.2).isSome = true ∧
        (fixtureCodeBytes (supportedNative branching).2.2.2).length ≤ 0xecc ∧
        (fixtureCodeBytes (supportedNative branching).2.2.2).length % 4 = 0
      rw [comparison_nativeCode]
      exact comparison_compiler_facts)
    (by
      rw [comparison_simpDeclarations]
      change (let optimized := (supportedAllocated branching).2
        let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
        let frame := (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false entry 1
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
        let frames := sptMapi (fun _ (argc,body) => (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false body argc
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
        Flapjack.Compiler.Backend.BackendProps.optionLe (Flapjack.Compiler.Backend.WordDepth.optionMap₂ max (some (max 1 (1+frame)))
          (Flapjack.Compiler.Backend.WordDepth.optionMap₂ (· + ·) (some 1) (Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172))
      rw [supportedAllocated_eq]
      have words : supportedWordPrograms branching = comparisonWordPrograms := by
        unfold supportedWordPrograms
        rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
        rfl
      have rows : (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2 =
          [(64,1,countdownOptimizedEntry),(65,1,.seq (.move 1 [(0,0)])
            (.seq .tick (.seq (.inst (.const 2 (7 : BitVec 64))) (.seq (.move 0 [(2,2)]) (.return 0 [2])))))] := by
        rw [comparison_optimized_table]
        with_unfolding_all rfl
      rw [words,rows]
      dsimp only
      have frames : sptMapi (fun _ (argc,body) => (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false body argc
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
          (sptFromAList [(64,1,countdownOptimizedEntry),(65,1,.seq (.move 1 [(0,0)])
            (.seq .tick (.seq (.inst (.const 2 (7 : BitVec 64))) (.seq (.move 0 [(2,2)]) (.return 0 [2])))))]) =
          sptFromAList [(64,0),(65,0)] := by with_unfolding_all rfl
      rw [frames]
      simp [Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth,
        Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
        sptLookup_sptFromAList,sptAListLookup,countdownOptimizedEntry]
      all_goals try (split <;> simp_all [sptLookup_sptFromAList,sptAListLookup])
      all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
      all_goals try simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,sptSize,sptFromAList,sptInsert]
      all_goals with_unfolding_all decide)
    (by
      rw [comparison_simpDeclarations]
      change 1 = (supportedNative branching).1.length
      rw [supported_native_bitmap branching branching_supported]
      rfl)
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiled,sourceRun,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [comparisonProduction,functionSourceProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compilerFinal,?_,machine,ffi,?_,outputEvents,?_⟩
  · simpa only [comparisonNative,comparisonOptimized] using compiled
  · dsimp only [comparisonTicks,comparisonNative,comparisonOptimized]
    exact machineRun
  · simpa [comparisonSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

def branchingLoopSourceFunctions : List (FunDeclOf 64) := [⟨"main",false,false,[],branchingLoop,.one⟩]
private def branchingLoopProduction := functionSourceProduction branchingLoopSourceFunctions 1 23
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem branchingLoop_countedRun (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler branchingLoopProduction.structs (countedFunctionsOfCode branchingLoopProduction.code)
      branchingLoopProduction.baseAddress branchingLoopProduction.topAddress panSemBitVec64BytesInWord 7 branchingLoopProduction.locals branchingLoopProduction.globals branchingLoopProduction.memory branchingLoopProduction.ffi branchingLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess branchingLoopProduction))
      (contracts := some (countedContractsOfCode branchingLoopProduction.code [])) =
      some (.returned branchingLoopProduction.locals branchingLoopProduction.globals branchingLoopProduction.memory branchingLoopProduction.ffi [.word 7],23) := by
  rw [supported_calls_irrel context primitive handler branchingLoopProduction.structs
    (countedFunctionsOfCode branchingLoopProduction.code) [] branchingLoopProduction.baseAddress branchingLoopProduction.topAddress
    panSemBitVec64BytesInWord 7 (some (panSemBitVec64MemoryAccess branchingLoopProduction))
    (some (countedContractsOfCode branchingLoopProduction.code [])) [] branchingLoop branchingLoop_supported.1]
  simpa [branchingLoopProduction,functionSourceProduction,sourceProduction,initialWordFor_one,
    executableState,singleEntrySourceProduction,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,
    panSemBitVec64WordModel,panSemWordModel,RiscV.panRiscVMemoryModel] using branchingLoop_source_run context primitive handler

open Flapjack.Basis.Pure.MlString
def branchingLoopHOLFunctions := branchingLoopSourceFunctions.map funDeclToHOL
def branchingLoopSimpFunctions := branchingLoopHOLFunctions.map (fun f => {f with body := panSimpCompileHOL f.body})
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem branchingLoop_noInline : (functionsHOL ((compileTopExactHOL (branchingLoopSimpFunctions.map DeclHOL.function) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  simp [branchingLoopSimpFunctions,branchingLoopHOLFunctions,branchingLoopSourceFunctions,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,branchingLoop,compileTopExactHOL,functionsHOL,
    compileTopFunctionLookup_eq_lookup,List.lookup,resortDeclsHOL,newMainNameHOL,isNameHOL,isDeclHOL,
    isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,
    compileExpExactHOL,inlinableHOL,functionsHOL]
private theorem branchingLoop_simpDeclarations : branchingLoopSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg branchingLoop)) := by
  rw [branchingLoop_simp_program]
  simp [branchingLoopSimpFunctions,branchingLoopHOLFunctions,branchingLoopSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,branchingLoop]
private theorem branchingLoop_nativeCode : (supportedNative branchingLoop).2.2.2 = branchingLoopNativeCode := by
  have words : supportedWordPrograms branchingLoop = branchWordPrograms := by
    unfold supportedWordPrograms
    rw [branchingLoop_simp_program,branchingLoop_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,branchingLoopNativeCode]
def branchingLoopSource := functionSourceExact branchingLoopSourceFunctions 1 23
private instance : DecidablePred branchingLoopSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
noncomputable def branchingLoopTicks : Nat :=
  let entries := functionsHOL (branchingLoopHOLFunctions.map DeclHOL.function)
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (branchingLoopSimpFunctions.map DeclHOL.function)).reverse
  let decls := branchingLoopSimpFunctions.map DeclHOL.function
  let lowered := compileTopExactHOL decls (ofString "main")
  let renamed := {branchingLoopSource with code := fpermCodeHOL (ofString "main") (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
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
  callPipelineTicks code bitmaps (max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs))
    (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg branchingLoop)))
    (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
    factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
    (max 1 (stackCodeWeight (sptFromAList code))) 23
def branchingLoopOptimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (branchingLoopSimpFunctions.map DeclHOL.function) (ofString "main")))))).2
def branchingLoopNative := compileNative riscvConfig false branchingLoopOptimized
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The branching loop reaches the machine through the call-aware theorem. -/
theorem branchingLoopFixture_machine : ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (branchingLoopHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes branchingLoopNative.2.2.2,branchingLoopNative.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart branchingLoopNative.2.2.2)) sourceFfi
      branchingLoopTicks (configuredMachineState branchingLoopNative.2.2.2 branchingLoopNative.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (branchingLoopHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  have shape : Supported branchingLoop := branchingLoop_supported.toSupported
  have table : FunctionTableSupported branchingLoopSourceFunctions := by
    intro f hf
    simp only [branchingLoopSourceFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
    subst f
    refine ⟨?_,shape.1,?_,rfl⟩
    · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,shape.2]
    · simp
  have unique : ((functionsHOL (branchingLoopHOLFunctions.map DeclHOL.function)).map Prod.fst).Nodup := by
    simp [branchingLoopHOLFunctions,branchingLoopSourceFunctions,funDeclToHOL,functionsHOL]
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (branchingLoopSimpFunctions.map DeclHOL.function)).reverse
  have span := countedCalls_initializedMachine shape branchingLoopProduction branchingLoopSource branchingLoopSourceFunctions 1 23 table rfl rfl targetCode
    (functionsHOL (branchingLoopHOLFunctions.map DeclHOL.function)) (by rfl)
    branchingLoopHOLFunctions rfl unique branchingLoopSimpFunctions rfl (ofString "main") rfl rfl
    (by simp [branchingLoopSource,functionSourceExact,branchingLoopSourceFunctions,funDeclToHOL,shapeToHOL,functionsHOL,
      HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,ofString])
    branchingLoop_noInline (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 7 23
    _ _ _ _ 7 (branchingLoop_countedRun _ _ _) (by rfl)
    (by
      rw [branchingLoop_simpDeclarations]
      change 0xa0020018 + (supportedNative branchingLoop).1.length*8 ≤ 0xa0410000
      rw [supported_native_bitmap branchingLoop branchingLoop_supported]
      decide)
    (by
      rw [branchingLoop_simpDeclarations]
      change fixtureStackSafe (supportedNative branchingLoop).2.2.2 = true
      rw [branchingLoop_nativeCode]
      exact branching_stackSafe)
    (by
      rw [branchingLoop_simpDeclarations]
      change (fixtureRemoveLabels (supportedNative branchingLoop).2.2.2).isSome = true ∧
        (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length ≤ 0xecc ∧
        (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length % 4 = 0
      rw [branchingLoop_nativeCode]
      exact branching_compiler_facts)
    (by
      rw [branchingLoop_simpDeclarations]
      change (let optimized := (supportedAllocated branchingLoop).2
        let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
        let frame := (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false entry 1
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
        let frames := sptMapi (fun _ (argc,body) => (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false body argc
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
        Flapjack.Compiler.Backend.BackendProps.optionLe (Flapjack.Compiler.Backend.WordDepth.optionMap₂ max (some (max 1 (1+frame)))
          (Flapjack.Compiler.Backend.WordDepth.optionMap₂ (· + ·) (some 1) (Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172))
      rw [supportedAllocated_eq]
      have words : supportedWordPrograms branchingLoop = branchWordPrograms := by
        unfold supportedWordPrograms
        rw [branchingLoop_simp_program,branchingLoop_crep_code]
        rfl
      have rows : (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 =
          [(64,1,countdownOptimizedEntry),(65,1,.seq (.move 1 [(0,0)])
            (.seq (.inst (.const 2 (2 : BitVec 64))) (.seq .tick (.seq (.move 0 [(0,0),(2,2)])
              (.seq (.loop ((Spt.ls PUnit.unit).bs PUnit.unit Spt.ln)
                (.seq (.move 0 [(2,2)]) (.seq (.ite .notEqual 2 (.imm 0)
                  (.seq (.move 0 [(2,2)]) (.seq (.inst (.const 4 (2 : BitVec 64)))
                    (.seq (.ite .equal 2 (.reg 4)
                      (.seq .tick (.seq (.inst (.const 2 (1 : BitVec 64))) (.move 1 [(2,2)])))
                      (.seq .tick (.seq (.inst (.const 2 (0 : BitVec 64))) (.move 1 [(2,2)]))))
                      (.seq .tick (.seq (.move 1 [(2,2)]) (.continue 0)))))) (.break 0))
                  (.seq .tick (.move 1 [(2,2)])))) (Spt.ls PUnit.unit))
                (.seq .tick (.seq (.inst (.const 2 (7 : BitVec 64))) (.seq (.move 0 [(2,2)]) (.return 0 [2])))))))))] := by
        rw [branch_optimized_table]
        with_unfolding_all rfl
      rw [words,rows]
      dsimp only
      have frames : sptMapi (fun _ (argc,body) => (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative riscvConfig false body argc
          (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
          (sptFromAList [(64,1,countdownOptimizedEntry),(65,1,.seq (.move 1 [(0,0)])
            (.seq (.inst (.const 2 (2 : BitVec 64))) (.seq .tick (.seq (.move 0 [(0,0),(2,2)])
              (.seq (.loop ((Spt.ls PUnit.unit).bs PUnit.unit Spt.ln)
                (.seq (.move 0 [(2,2)]) (.seq (.ite .notEqual 2 (.imm 0)
                  (.seq (.move 0 [(2,2)]) (.seq (.inst (.const 4 (2 : BitVec 64)))
                    (.seq (.ite .equal 2 (.reg 4)
                      (.seq .tick (.seq (.inst (.const 2 (1 : BitVec 64))) (.move 1 [(2,2)])))
                      (.seq .tick (.seq (.inst (.const 2 (0 : BitVec 64))) (.move 1 [(2,2)]))))
                      (.seq .tick (.seq (.move 1 [(2,2)]) (.continue 0)))))) (.break 0))
                  (.seq .tick (.move 1 [(2,2)])))) (Spt.ls PUnit.unit))
                (.seq .tick (.seq (.inst (.const 2 (7 : BitVec 64))) (.seq (.move 0 [(2,2)]) (.return 0 [2])))))))))]) =
          sptFromAList [(64,0),(65,0)] := by with_unfolding_all rfl
      rw [frames]
      simp [Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth,
        Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
        sptLookup_sptFromAList,sptAListLookup,countdownOptimizedEntry]
      all_goals try (split <;> simp_all [sptLookup_sptFromAList,sptAListLookup])
      all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
      all_goals try simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,sptSize,sptFromAList,sptInsert]
      all_goals with_unfolding_all decide)
    (by
      rw [branchingLoop_simpDeclarations]
      change 1 = (supportedNative branchingLoop).1.length
      rw [supported_native_bitmap branchingLoop branchingLoop_supported]
      rfl)
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiled,sourceRun,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [branchingLoopProduction,functionSourceProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compilerFinal,?_,machine,ffi,?_,outputEvents,?_⟩
  · simpa only [branchingLoopNative,branchingLoopOptimized] using compiled
  · dsimp only [branchingLoopTicks,branchingLoopNative,branchingLoopOptimized]
    exact machineRun
  · simpa [branchingLoopSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

private theorem natural_callee (n : Nat) : supportedCallee (naturalCountdownHOL n) = naturalCountdownCrepBody (BitVec.ofNat 64 n) := by
  have h := supported_crepPrograms (naturalCountdown n) (naturalCountdown_supported n)
  change crepPrograms (naturalCountdownHOL n) = _ at h
  rw [natural_countdown_crep_code] at h
  simpa [twoPrograms,naturalCountdownHOL] using h.symm

private theorem countdown_words (n : Nat) : supportedWordPrograms (countdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  rw [countdown_simp_program]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl

private theorem countdown_native (n : Nat) : (supportedNative (countdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,countdown_words,countdownNativeStackCode]

private theorem countdown_frame (n : Nat) : supportedCalleeFrame (countdown n) ≤
    (fixtureStack (supportedNative (countdown n)).2.2.2 (fixtureCompilerConfig (supportedNative (countdown n)).2.2.2)).stack.length := by
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,countdown_words,countdownOptimizedLoop_lookup]
  dsimp only
  rw [nativeEntryFrameSize_compile]
  change 1 + nativeEntryFrameSize countdownZeroLimit (countdownOptimizedLoop n) ≤ _
  rw [countdownCallee_entryFrame_zero]
  exact fixtureStack_nonempty _ _

private theorem countdown_crepBudget (n : Nat) : supportedCrepBudget (countdown n) (6*n+9) = 3+8*(6*n+18) := by
  unfold supportedCrepBudget
  rw [countdown_simp_program]
  change 3 + CrepSteps.statementWeight (supportedCallee (naturalCountdownHOL n)) *
    (6*n+9+1+CrepSteps.statementWeight (supportedCallee (naturalCountdownHOL n))) = _
  rw [natural_callee]
  simp [naturalCountdownCrepBody,CrepSteps.statementWeight]

private theorem countdown_loopBudget (n : Nat) : supportedLoopBudget (countdown n) (6*n+9) = countdownLoopBudget n := by
  unfold supportedLoopBudget countdownLoopBudget
  rw [countdown_simp_program]
  dsimp only
  change 3 * loopVisitWeight (optimiseHOL (compileHOLExact _ .ln (supportedCallee (naturalCountdownHOL n)))) * _ = _
  rw [natural_callee]
  have weight := countdown_optimized_weight riscvConfig.isa n
  change loopVisitWeight (optimiseHOL (compileHOLExact (ctxtFcExact
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).target
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).funcs [] []) .ln
    (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 at weight
  rw [weight,countdown_crepBudget]

private theorem countdown_loopVisits (n : Nat) : supportedLoopVisits (countdown n) (6*n+9) = countdownLoopVisits n := by
  unfold supportedLoopVisits countdownLoopVisits
  rw [countdown_simp_program]
  dsimp only
  change loopVisitWeight (optimiseHOL (compileHOLExact _ .ln (supportedCallee (naturalCountdownHOL n)))) * _ + 8 = _
  rw [natural_callee]
  have weight := countdown_optimized_weight riscvConfig.isa n
  change loopVisitWeight (optimiseHOL (compileHOLExact (ctxtFcExact
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).target
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).funcs [] []) .ln
    (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 at weight
  rw [weight,countdown_crepBudget,countdown_loopBudget]

private theorem countdown_wordBound (n : Nat) : supportedWordBound (countdown n) (6*n+9) = countdownWordBound n := by
  unfold supportedWordBound countdownWordBound
  rw [countdown_simp_program]
  dsimp only
  change twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (supportedCallee (naturalCountdownHOL n)) (supportedLoopVisits (countdown n) (6*n+9)) phase3WordConfig riscvConfig = _
  rw [natural_callee,countdown_loopVisits]
  rfl

private theorem countdown_stackBound (n : Nat) : supportedStackBound (countdown n) (6*n+9) = 9543650688*n+29426459323 := by
  unfold supportedStackBound
  rw [countdown_words,countdown_wordBound]
  have entryEq : supportedEntry = countdownSourceWordEntry n := by with_unfolding_all rfl
  rw [entryEq]
  rw [countdown_stackBound_closed,countdown_bound_closed]
  omega

private theorem countdown_ticks (n : Nat) : supportedMachineFactor (countdown n) * (6*n+9) + supportedMachineOffset (countdown n) =
    167602730287449600*(6*n+9)+1592247331570371948 := by
  rw [← supportedMachineTicks_affine]
  unfold supportedMachineTicks
  rw [countdown_native,countdown_stackBound]
  dsimp only
  rw [countdownLabTick_closed]
  omega


def countdownSourceFunctions (n : Nat) : List (FunDeclOf 64) := [⟨"main",false,false,[],countdown n,.one⟩]
private def countdownProduction (n : Nat) := functionSourceProduction (countdownSourceFunctions n) 1 (6*n+9)
def countdownSource (n : Nat) := functionSourceExact (countdownSourceFunctions n) 1 (6*n+9)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem countdown_countedRun (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ result, evalPanValueFfiProgSteps context primitive handler (countdownProduction n).structs (countedFunctionsOfCode (countdownProduction n).code)
      (countdownProduction n).baseAddress (countdownProduction n).topAddress panSemBitVec64BytesInWord (n+4) (countdownProduction n).locals (countdownProduction n).globals (countdownProduction n).memory (countdownProduction n).ffi (countdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (countdownProduction n)))
      (contracts := some (countedContractsOfCode (countdownProduction n).code [])) = some (result,6*n+9) ∧
      result = .returned (restorePanValueLocal (fun _ => none) "x" ((countdownProduction n).locals "x"))
        (countdownProduction n).globals (countdownProduction n).memory (countdownProduction n).ffi [.word 0] := by
  let _ : DecidablePred (countdownSource n).memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have rel := functionSource_related (countdownSourceFunctions n) 1 (6*n+9) (by
    intro f hf; simp [countdownSourceFunctions] at hf; subst f; simp [NameRanged])
  have ranged : PanSemStateRelExecRanged (countdownProduction n) := by
    simp [PanSemStateRelExecRanged,countdownProduction,functionSourceProduction,sourceProduction,StructContextByteRanged,StructContext.toHOL]
  have h := counted_decl_countdown_return n (countdownProduction n) (countdownSource n) rel ranged "x" countdown_name_ranged range (by simp [countdownSource,functionSourceExact]; omega)
    0 (mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty) context primitive handler
    (countedFunctionsOfCode (countdownProduction n).code) 0
  obtain ⟨result,final,run,hol,bound,shape,ret⟩ := h
  refine ⟨result,?_,ret⟩
  rw [supported_calls_irrel context primitive handler (countdownProduction n).structs (countedFunctionsOfCode (countdownProduction n).code) (countedFunctionsOfCode (countdownProduction n).code)
    (countdownProduction n).baseAddress (countdownProduction n).topAddress panSemBitVec64BytesInWord (n+4)
    (some (panSemBitVec64MemoryAccess (countdownProduction n))) (some (countedContractsOfCode (countdownProduction n).code [])) [] (countdown n) (countdown_supported n).1]
  simpa [countdown] using run

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
def countdownHOLFunctions (n : Nat) := (countdownSourceFunctions n).map funDeclToHOL
def countdownSimpFunctions (n : Nat) := (countdownHOLFunctions n).map (fun f => {f with body := panSimpCompileHOL f.body})
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem countdown_noInline (n : Nat) : (functionsHOL ((compileTopExactHOL ((countdownSimpFunctions n).map DeclHOL.function) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  simp [countdownSimpFunctions,countdownHOLFunctions,countdownSourceFunctions,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,countdown,countdownBody,compileTopExactHOL,functionsHOL,
    compileTopFunctionLookup_eq_lookup,List.lookup,resortDeclsHOL,newMainNameHOL,isNameHOL,isDeclHOL,
    isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,
    compileExpExactHOL,inlinableHOL,functionsHOL]
private theorem countdown_simpDeclarations (n : Nat) : (countdownSimpFunctions n).map DeclHOL.function = declarations (progToHOL (panSimpProg (countdown n))) := by
  rw [countdown_simp_program]
  simp [countdownSimpFunctions,countdownHOLFunctions,countdownSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,countdown,naturalCountdown,countdownBody]
private theorem countdown_wordsGeneral (n : Nat) : supportedWordPrograms (countdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  rw [countdown_simp_program]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl
private def countdownRaw (n : Nat) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL ((countdownSimpFunctions n).map DeclHOL.function) (ofString "main"))))
private theorem countdown_rawEq (n : Nat) : countdownRaw n = supportedWordPrograms (countdown n) := by
  simp only [countdownRaw,countdown_simpDeclarations,supportedWordPrograms,crepPrograms]
private theorem countdown_nativeRawEq (n : Nat) : compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (countdownRaw n)).2 = supportedNative (countdown n) := by
  rw [countdown_rawEq n]
  rfl
private theorem countdown_nativeCodeGeneral (n : Nat) : (supportedNative (countdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,countdown_wordsGeneral,countdownNativeStackCode]

open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable SteppedFlapjack.WordToStackSteps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem countdown_capacity (n : Nat) :
  let optimized := (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2
  let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
  optionLe (optionMap₂ max (some (max 1 (1+frame))) (optionMap₂ (· + ·) (some 1)
    (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172) := by
  rw [countdown_optimized_literal]
  have table : countdownOptimizedLiteral (BitVec.ofNat 64 n) =
      [(64,1,countdownOptimizedEntry),(65,1,countdownOptimizedLoop n)] := by
    simp [countdownOptimizedLiteral,countdownOptimizedEntry,countdownOptimizedLoop]
  rw [table]
  have entryFrame : (compileProgNative riscvConfig false countdownOptimizedEntry 1
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 = 0 := by
    with_unfolding_all rfl
  have calleeFrame : (compileProgNative riscvConfig false (countdownOptimizedLoop n) 1
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1 = 0 := by
    change (compileProgNative riscvConfig false (countdownOptimizedLoop n) 1 countdownZeroLimit (.nil,0)).2.1 = 0
    rw [nativeEntryFrameSize_compile]
    exact countdownCallee_entryFrame_zero n
  have frames : sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
      (sptFromAList [(64,1,countdownOptimizedEntry),(65,1,countdownOptimizedLoop n)]) = sptFromAList [(64,0),(65,0)] := by
    simp [sptFromAList,sptInsert,sptMapi,sptMapi0,sptMkBN,entryFrame,calleeFrame]
  dsimp only
  rw [frames]
  simp [fullCallGraphDepth,callGraphDepth,sptLookup_sptFromAList,sptAListLookup,countdownOptimizedEntry]
  all_goals try (split <;> simp_all [sptLookup_sptFromAList,sptAListLookup])
  all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
  all_goals try simp [callGraphDepth,sptSize,sptFromAList,sptInsert,countdownOptimizedLoop,countdownOptimizedLiteral]
  all_goals with_unfolding_all decide

noncomputable def countdownTicks (n : Nat) : Nat :=
  let entries := functionsHOL ((countdownHOLFunctions n).map DeclHOL.function)
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL ((countdownSimpFunctions n).map DeclHOL.function)).reverse
  let decls := (countdownSimpFunctions n).map DeclHOL.function
  let lowered := compileTopExactHOL decls (ofString "main")
  let renamed := {(countdownSource n) with code := fpermCodeHOL (ofString "main") (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let programs := compileProgDeclsHOLW lowered
  let crep := compileProgExactHOLW panCtxt p
  let countdownRaw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig countdownRaw).2
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
  callPipelineTicks code bitmaps (max (CrepSteps.statementWeight crep) (CrepSteps.codeWeight programs))
    (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg (countdown n))))
    (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
    factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
    (max 1 (stackCodeWeight (sptFromAList code))) (6*n+9)
def countdownOptimized (n : Nat) := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL ((countdownSimpFunctions n).map DeclHOL.function) (ofString "main")))))).2
def countdownNative (n : Nat) := compileNative riscvConfig false (countdownOptimized n)

-- The compiler declarations retain the width proof synthesized for the first
-- witness; normalize it once before matching the polymorphic compiler theorem.
set_option linter.auxLemma false in
private theorem witnessWidthProof : comparisonHOLFunctions._proof_1 = @Nat.instNeZeroSucc 63 :=
  Subsingleton.elim _ _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
/-- The countdown reaches the initialized machine through the call-aware theorem. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      ((countdownHOLFunctions n).map DeclHOL.function) = some (fixtureCodeBytes (countdownNative n).2.2.2,(countdownNative n).1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (countdownNative n).2.2.2)) sourceFfi
      (countdownTicks n) (configuredMachineState (countdownNative n).2.2.2 (countdownNative n).1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        ((countdownHOLFunctions n).map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  let _ : DecidablePred (countdownSource n).memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have shape : Supported (countdown n) := (countdown_supported n).toSupported
  have table : FunctionTableSupported (countdownSourceFunctions n) := by
    intro f hf
    simp only [countdownSourceFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
    subst f
    refine ⟨?_,shape.1,?_,rfl⟩
    · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,shape.2]
    · simp
  have unique : ((functionsHOL ((countdownHOLFunctions n).map DeclHOL.function)).map Prod.fst).Nodup := by
    simp [countdownHOLFunctions,countdownSourceFunctions,funDeclToHOL,functionsHOL]
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL ((countdownSimpFunctions n).map DeclHOL.function)).reverse
  obtain ⟨result,sourceRun,ret⟩ := countdown_countedRun n range (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  rw [ret] at sourceRun
  have span := countedCalls_initializedMachine shape (countdownProduction n) (countdownSource n) (countdownSourceFunctions n) 1 (6*n+9) table rfl rfl targetCode
    (functionsHOL ((countdownHOLFunctions n).map DeclHOL.function)) (by rfl)
    (countdownHOLFunctions n) rfl unique (countdownSimpFunctions n) rfl (ofString "main") rfl rfl
    (by simp [countdownSource,functionSourceExact,countdownSourceFunctions,funDeclToHOL,shapeToHOL,functionsHOL,
      HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,ofString])
    (countdown_noInline n) (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] (n+4) (6*n+9)
    _ _ _ _ 0 sourceRun (by rfl)
    (by
      dsimp only
      rw [← countdownRaw, countdown_nativeRawEq n, supported_native_bitmap (countdown n) (countdown_supported n)]
      decide)
    (by
      dsimp only
      rw [← countdownRaw, countdown_nativeRawEq n, countdown_nativeCodeGeneral n]
      exact countdown_stackSafe n)
    (by
      dsimp only
      rw [← countdownRaw, countdown_nativeRawEq n, countdown_nativeCodeGeneral n]
      exact countdown_compiler_facts n)
    (by
      dsimp only
      rw [← countdownRaw, countdown_rawEq n, ← supportedAllocated, supportedAllocated_eq, countdown_wordsGeneral]
      exact countdown_capacity n)
    (by
      dsimp only
      rw [← countdownRaw, countdown_nativeRawEq n, supported_native_bitmap (countdown n) (countdown_supported n)]
      rfl)
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiled,sourceResult,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [countdownProduction,functionSourceProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compilerFinal,?_,machine,ffi,?_,outputEvents,?_⟩
  · unfold countdownNative countdownOptimized
    rw [witnessWidthProof]
    exact compiled
  · dsimp only [countdownTicks,countdownNative,countdownOptimized]
    rw [witnessWidthProof]
    exact machineRun
  · simpa [countdownSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

private theorem natural_simp (n : Nat) : panSimpProg (naturalCountdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]

private theorem natural_words (n : Nat) : supportedWordPrograms (naturalCountdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  rw [natural_simp]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl

private theorem natural_native (n : Nat) : (supportedNative (naturalCountdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,natural_words,countdownNativeStackCode]

private theorem natural_frame (n : Nat) : supportedCalleeFrame (naturalCountdown n) ≤
    (fixtureStack (supportedNative (naturalCountdown n)).2.2.2 (fixtureCompilerConfig (supportedNative (naturalCountdown n)).2.2.2)).stack.length := by
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,natural_words,countdownOptimizedLoop_lookup]
  dsimp only
  rw [nativeEntryFrameSize_compile]
  change 1 + nativeEntryFrameSize countdownZeroLimit (countdownOptimizedLoop n) ≤ _
  rw [countdownCallee_entryFrame_zero]
  exact fixtureStack_nonempty _ _

private theorem natural_wordBound_eq (n budget : Nat) :
    supportedWordBound (naturalCountdown n) budget = supportedWordBound (countdown n) budget := by
  simp only [supportedWordBound,supportedLoopVisits,supportedLoopBudget,supportedCrepBudget,natural_simp,countdown_simp_program]

private theorem natural_ticks (n : Nat) : supportedMachineFactor (naturalCountdown n) * (6*n+9) + supportedMachineOffset (naturalCountdown n) =
    167602730287449600*(6*n+9)+1592247331570371948 := by
  rw [← supportedMachineTicks_affine,← countdown_ticks,← supportedMachineTicks_affine]
  unfold supportedMachineTicks supportedStackBound
  rw [natural_native,countdown_native,natural_words,countdown_words,natural_wordBound_eq]

/-- The natural countdown is independently instantiated from the Phase 7 theorem. -/
theorem naturalCountdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL (naturalCountdown n))) = some (fixtureCodeBytes (countdownNativeStackCode n),[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600*(6*n+9)+1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL (naturalCountdown n))).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL (naturalCountdown n))) = .terminate .success ffiPost.ioEvents := by
  have actual := counted_decl_countdown_simplified n (executableState (naturalCountdownHOL n))
    (exactState (naturalCountdownHOL n)) (source_related _) (source_ranged _) "x" countdown_name_ranged range
    (by change n ≤ 2^64; omega) 0 witnessContext witnessPrimitive witnessHandler [] 0
  obtain ⟨result,_,sourceRun,_,_,resultEq⟩ := actual
  subst result
  have run : evalPanValueFfiProgSteps witnessContext witnessPrimitive witnessHandler (executableState (progToHOL (naturalCountdown n))).structs []
      (executableState (progToHOL (naturalCountdown n))).baseAddress (executableState (progToHOL (naturalCountdown n))).topAddress
      panSemBitVec64BytesInWord (n+3) (executableState (progToHOL (naturalCountdown n))).locals
      (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
      (executableState (progToHOL (naturalCountdown n))).ffi (naturalCountdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (naturalCountdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (naturalCountdown n))).locals "x"))
          (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
          (executableState (progToHOL (naturalCountdown n))).ffi [.word 0],6*n+7) := by
    simpa [naturalCountdownHOL,naturalCountdown] using sourceRun
  have safe : fixtureStackSafe (supportedNative (naturalCountdown n)).2.2.2 = true := by
    rw [natural_native]
    exact countdown_stackSafe n
  have facts : (fixtureRemoveLabels (supportedNative (naturalCountdown n)).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative (naturalCountdown n)).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative (naturalCountdown n)).2.2.2).length % 4 = 0 := by
    rw [natural_native]
    exact countdown_compiler_facts n
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine (naturalCountdown n) (naturalCountdown_supported n) witnessContext witnessPrimitive witnessHandler
      (n+3) (6*n+7) (6*n+9) _ _ _ _ 0 run (by omega) (natural_frame n) safe facts
  rw [natural_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [natural_native] using compiled,
    machinePost,ffiPost,by simpa only [natural_native] using machineRun,events,semantics⟩

end SteppedFlapjack.Concrete
