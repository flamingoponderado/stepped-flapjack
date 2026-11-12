import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.SingletonMachine
import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.Concrete.BranchingFrames
import SteppedFlapjack.Concrete.CountdownOptimized
import SteppedFlapjack.Concrete.CountdownLabBounds
import SteppedFlapjack.Concrete.BranchEntryLoop
import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop
import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound

/-! Concrete instances of the supported source-to-machine theorem. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordToStackSteps

open SteppedFlapjack.LoopLiveSteps

private theorem entrySyntaxWeight (ctx : CrepToLoopContextExact) (name : MlString) :
    callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
  simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]

private theorem entryOptimizedWeight (ctx : CrepToLoopContextExact) (name : MlString) :
    loopVisitWeight (optimiseHOL (compileHOLExact ctx .ln (.seq .skip (.call none name []) : CrepProgHOL 64))) = 10 := by
  have generic (lab : Nat) : loopVisitWeight (optimiseHOL
      (.seq .skip (.seq (.call none (some lab) [] none) .skip) : HolLoopProg 64)) = 10 := by
    simp [optimiseHOL,loopCallCompHOL,Flapjack.compHOL,shrinkHOL,markAllHOL,loopVisitWeight]
  simpa [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL] using generic (findLabExact ctx name)

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
private theorem comparison_simpDeclarations : comparisonSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg branching)) := by
  rw [branching_simp_program]
  simp [comparisonSimpFunctions,comparisonHOLFunctions,comparisonSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,branching]
private theorem comparison_nativeCode : (supportedNative branching).2.2.2 = comparisonNativeCode := by
  have words : supportedWordPrograms branching = comparisonWordPrograms := by
    unfold supportedWordPrograms
    rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,comparisonNativeCode]
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
def comparisonOptimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (comparisonSimpFunctions.map DeclHOL.function) (ofString "main")))))).2
def comparisonNative := compileNative riscvConfig false comparisonOptimized
section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem sameNative : comparisonNative = supportedNative branching := by
  unfold comparisonNative comparisonOptimized supportedNative supportedAllocated supportedWordPrograms crepPrograms
  rw [comparison_simpDeclarations]

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackToLabSteps
private theorem sameCode : comparisonNative.2.2.2 = comparisonNativeCode := by
  rw [sameNative]
  have words : supportedWordPrograms branching = comparisonWordPrograms := by
    unfold supportedWordPrograms
    rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,comparisonNativeCode]
private theorem cmpFactor (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf comparisonNative.2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [sameCode]
  unfold comparisonNativeCode
  rw [comparison_optimized_table,riscvNative_two_entry_code]
  decide +kernel

open Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
open SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.StackRemove
private theorem cmpStackWeight : stackCodeWeight (sptFromAList comparisonNative.2.2.2) = 15 := by
  rw [sameCode]
  unfold comparisonNativeCode
  rw [comparison_optimized_table,riscvNative_two_entry_code]
  decide +kernel
private theorem cmpOpt : comparisonOptimized = (supportedAllocated branching).2 := by
  unfold comparisonOptimized supportedAllocated supportedWordPrograms crepPrograms
  rw [comparison_simpDeclarations]
private theorem cmpWordWeight : wordCodeWeight (sptFromAList comparisonOptimized) = 9 := by
  have words : supportedWordPrograms branching = comparisonWordPrograms := by
    unfold supportedWordPrograms
    rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
    rfl
  rw [cmpOpt,supportedAllocated_eq,words,comparison_optimized_table]
  decide +kernel
private theorem cmpCodeWeight (name : MlString) : CrepSteps.codeWeight (twoPrograms (ofString "main") name branchCrepBody) = 3 := by
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms,branchCrepBody]
private theorem cmpRate (ctx : CrepToLoopContextExact) (name : MlString) (clock : Nat) :
    callClockFactor ctx ((twoPrograms (ofString "main") name branchCrepBody).map (fun row => (row.2.1,row.2.2)))
      clock (.seq .skip (.call none name [])) = 192 := by
  have entry : callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
    simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
  have table : callTableCost ctx ((twoPrograms (ofString "main") name branchCrepBody).map (fun row => (row.2.1,row.2.2))) = 24 := by
    simp [callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,branchCrepBody,
      compileExpHOLExact,compileExpsHOLExact,progIfHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
  simp [callClockFactor,entry,table]
private theorem cmpRateRaw (ctx : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor ctx (([(ofString "main",[],.seq .skip (.call none (entryName branchingHOL) [])),
   (entryName branchingHOL,[],.ite (.cmp .lower (.const 0) (.const 1)) (.return [.const 7]) (.return [.const 9]))] : List (MlString × List Nat × CrepProgHOL 64)).map (fun row => (row.2.1,row.2.2))) clock
      (.seq .skip (.call none (entryName branchingHOL) [])) = 192 := by
  simpa only [twoPrograms,branchCrepBody] using cmpRate ctx (entryName branchingHOL) clock
private theorem cmpCodeWeightRaw : CrepSteps.codeWeight ([(ofString "main",[],.seq .skip (.call none (entryName branchingHOL) [])),
   (entryName branchingHOL,[],.ite (.cmp .lower (.const 0) (.const 1)) (.return [.const 7]) (.return [.const 9]))] : List (MlString × List Nat × CrepProgHOL 64)) = 3 := by
  simpa only [twoPrograms,branchCrepBody] using cmpCodeWeight (entryName branchingHOL)
private theorem cmpLoopWeightRaw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    ([(ofString "main",[],.seq .skip (.call none (entryName branchingHOL) [])),
      (entryName branchingHOL,[],.ite (.cmp .lower (.const 0) (.const 1)) (.return [.const 7]) (.return [.const 9]))] : List (MlString × List Nat × CrepProgHOL 64)))) = 46 := by
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    (twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody))) = 46
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody branching_scalar,
    twoLoops_exact riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody (Ne.symm (entryName_fresh branchingHOL))]
  with_unfolding_all decide
private theorem loopCodeProjection {σ : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (source : CrepSemHOLState 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64)) :
    (concreteDeclLoopState arch source programs).code = sptFromAList (compileProgHOLExact arch programs) := rfl
private theorem crepClockProjection {σ : Type} (source : PanSemStateFiniteExact 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64)) :
    (concreteDeclCrepState source programs).clock = source.clock := rfl
private theorem setupClockProjection {σ : Type} (source : PanSemStateFiniteExact 64 σ) code :
    (noGlobalsLoweredPreCall source code).clock = source.clock+1 := rfl


end

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
section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem branchSameNative : branchingLoopNative = supportedNative branchingLoop := by
  unfold branchingLoopNative branchingLoopOptimized supportedNative supportedAllocated supportedWordPrograms crepPrograms
  rw [branchingLoop_simpDeclarations]

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackToLabSteps
private theorem branchSameCode : branchingLoopNative.2.2.2 = branchingLoopNativeCode := by
  rw [branchSameNative]
  have words : supportedWordPrograms branchingLoop = branchWordPrograms := by
    unfold supportedWordPrograms
    rw [branchingLoop_simp_program,branchingLoop_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,branchingLoopNativeCode]
private theorem branchSameBitmap : branchingLoopNative.1 = [4] := by
  rw [branchSameNative, supported_native_bitmap branchingLoop branchingLoop_supported]
private theorem brcFactor (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf branchingLoopNative.2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [branchSameCode]
  unfold branchingLoopNativeCode
  rw [branch_optimized_table,riscvNative_two_entry_code]
  decide +kernel

open Flapjack.Basis.Pure.MlString
private theorem brcPrograms : compileProgDeclsHOLW (compileTopExactHOL (branchingLoopSimpFunctions.map DeclHOL.function) (ofString "main")) = crepPrograms (progToHOL branchingLoop) := by
  rw [branchingLoop_simpDeclarations,branchingLoop_simp_program]
  rfl
private theorem brcMain : newMainNameHOL (branchingLoopSimpFunctions.map DeclHOL.function) = entryName (progToHOL branchingLoop) := by
  rw [branchingLoop_simpDeclarations,branchingLoop_simp_program]
  rfl

open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
open SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.StackRemove
private theorem brcStackWeight : stackCodeWeight (sptFromAList branchingLoopNative.2.2.2) = 48 := by
  rw [branchSameCode]
  unfold branchingLoopNativeCode
  rw [branch_optimized_table,riscvNative_two_entry_code]
  decide +kernel
private theorem brcOpt : branchingLoopOptimized = (supportedAllocated branchingLoop).2 := by
  unfold branchingLoopOptimized supportedAllocated supportedWordPrograms crepPrograms
  rw [branchingLoop_simpDeclarations]
private theorem brcWordWeight : wordCodeWeight (sptFromAList branchingLoopOptimized) = 46 := by
  have words : supportedWordPrograms branchingLoop = branchWordPrograms := by
    unfold supportedWordPrograms
    rw [branchingLoop_simp_program,branchingLoop_crep_code]
    rfl
  rw [brcOpt,supportedAllocated_eq,words,branch_optimized_table]
  decide +kernel
private theorem brcTableWeight : SimpVisits.simpTableFactor (functionsHOL (branchingLoopHOLFunctions.map DeclHOL.function)) = 8 := by
  simp [branchingLoopHOLFunctions,branchingLoopSourceFunctions,funDeclToHOL,functionsHOL,SimpVisits.simpTableFactor,
    panSimpCompileHOL,seqAssocHOL,retToTailHOL,smartSeqHOL,seqCallRetHOL,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw,branchingLoop]
private theorem brcBodyWeight : SimpVisits.hw (progToHOL (panSimpProg branchingLoop)) = 7 := by
  rw [branchingLoop_simp_program]
  simp [branchingLoop,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw]
private theorem brcClock : branchingLoopSource.clock = 23 := by rfl
private theorem brcCodeWeight (name : MlString) : CrepSteps.codeWeight (twoPrograms (ofString "main") name branchingLoopCrepBody) = 11 := by
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms,branchingLoopCrepBody]
private theorem brcRate (ctx : CrepToLoopContextExact) (name : MlString) (clock : Nat) :
    callClockFactor ctx ((twoPrograms (ofString "main") name branchingLoopCrepBody).map (fun row => (row.2.1,row.2.2)))
      clock (.seq .skip (.call none name [])) = 306 := by
  have entry : callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
    simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
  have table : callTableCost ctx ((twoPrograms (ofString "main") name branchingLoopCrepBody).map (fun row => (row.2.1,row.2.2))) = 43 := by
    simp [callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,branchingLoopCrepBody,
      compileExpHOLExact,compileExpsHOLExact,progIfHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
  simp [callClockFactor,entry,table]
private theorem brcRateRaw (ctx : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor ctx (([(ofString "main",[],.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])),
   (entryName (progToHOL branchingLoop),[],branchingLoopCrepBody)] : List (MlString × List Nat × CrepProgHOL 64)).map (fun row => (row.2.1,row.2.2))) clock
      (.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])) = 306 := by
  simpa only [twoPrograms] using brcRate ctx (entryName (progToHOL branchingLoop)) clock
private theorem brcCodeWeightRaw : CrepSteps.codeWeight ([(ofString "main",[],.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])),
   (entryName (progToHOL branchingLoop),[],branchingLoopCrepBody)] : List (MlString × List Nat × CrepProgHOL 64)) = 11 := by
  simpa only [twoPrograms] using brcCodeWeight (entryName (progToHOL branchingLoop))
private theorem brcLoopWeightRaw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    ([(ofString "main",[],.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])),
      (entryName (progToHOL branchingLoop),[],branchingLoopCrepBody)] : List (MlString × List Nat × CrepProgHOL 64)))) = 80 := by
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    (twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody))) = 80
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody branchingLoop_scalar,
    twoLoops_exact riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop)))]
  with_unfolding_all decide
private theorem branchingLoop_ticks_numeric : branchingLoopTicks = 12798071459382541821948 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold branchingLoopTicks callPipelineTicks
  dsimp only
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  rw [← branchingLoopOptimized, ← branchingLoopNative, branchSameBitmap]
  have factor := brcFactor (fixtureCompilerConfig branchingLoopNative.2.2.2)
  unfold fixtureStackOracle at factor
  rw [factor, uniform, init]
  rw [brcPrograms,brcMain,branchingLoop_crep_code]
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
  rw [entryOptimizedWeight,brcStackWeight,brcWordWeight]
  simp only [brcTableWeight,brcBodyWeight]
  simp only [brcRateRaw,entrySyntaxWeight,brcCodeWeightRaw]
  simp only [loopCodeProjection,crepClockProjection,setupClockProjection,brcLoopWeightRaw,brcClock]
  simp [CrepSteps.statementWeight,flattenStepFactor]


end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The branching loop reaches the machine through the call-aware theorem. -/
theorem branchingLoopFixture_machine : ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (branchingLoopHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes branchingLoopNative.2.2.2,branchingLoopNative.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart branchingLoopNative.2.2.2)) sourceFfi
      12798071459382541821948 (configuredMachineState branchingLoopNative.2.2.2 branchingLoopNative.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (branchingLoopHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  have shape : ScalarSupported branchingLoop := branchingLoop_supported.toScalarSupported
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
  · rw [← branchingLoop_ticks_numeric]
    dsimp only [branchingLoopTicks,branchingLoopNative,branchingLoopOptimized]
    exact machineRun
  · simpa [branchingLoopSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

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

private theorem countdownOptimized_literal (n : Nat) :
    countdownOptimized n = countdownOptimizedLiteral (BitVec.ofNat 64 n) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  unfold countdownOptimized
  change (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (countdownRaw n)).2 = _
  rw [countdown_rawEq, countdown_wordsGeneral, compileWith_eq_compile _ allocator, phase3WordConfig_eq,
    countdown_optimized_literal]

private theorem countdownNative_literal (n : Nat) : (countdownNative n).2.2.2 = countdownNativeStackCode n := by
  unfold countdownNative countdownNativeStackCode
  rw [countdownOptimized_literal, countdown_optimized_literal]

private theorem countdownNative_bitmap (n : Nat) : (countdownNative n).1 = [4] := by
  unfold countdownNative countdownOptimized
  change (compileNative riscvConfig false (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (countdownRaw n)).2).1 = _
  rw [countdown_nativeRawEq, supported_native_bitmap (countdown n) (countdown_supported n)]

private theorem countdownLiteral_syntaxTableWeight (ctx : CrepToLoopContextExact) (name : MlString) (n : Nat) :
    callTableCost ctx ((twoPrograms (ofString "main") name (naturalCountdownCrepBody (BitVec.ofNat 64 n))).map (fun row => (row.2.1,row.2.2))) = 28 := by
  simp [callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,naturalCountdownCrepBody,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]

private theorem countdownLiteral_sourceCodeWeight (name : MlString) (n : Nat) :
    CrepSteps.codeWeight (twoPrograms (ofString "main") name (naturalCountdownCrepBody (BitVec.ofNat 64 n))) = 8 := by
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms,naturalCountdownCrepBody]

private theorem countdownLiteral_rate (ctx : CrepToLoopContextExact) (name : MlString) (n clock : Nat) :
    callClockFactor ctx ((twoPrograms (ofString "main") name (naturalCountdownCrepBody (BitVec.ofNat 64 n))).map (fun row => (row.2.1,row.2.2)))
      clock (.seq .skip (.call none name [])) = 216 := by
  simp [callClockFactor,entrySyntaxWeight,countdownLiteral_syntaxTableWeight]

private theorem countdownLiteral_programs (n : Nat) : crepPrograms (naturalCountdownHOL n) =
    twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (naturalCountdownCrepBody (BitVec.ofNat 64 n)) := by
  rw [natural_countdown_crep_code]
  rfl

private theorem countdown_sourceTableWeight (n : Nat) :
    SimpVisits.simpTableFactor (functionsHOL ((countdownHOLFunctions n).map DeclHOL.function)) = 6 := by
  simp [countdownHOLFunctions,countdownSourceFunctions,funDeclToHOL,functionsHOL,SimpVisits.simpTableFactor,
    panSimpCompileHOL,seqAssocHOL,retToTailHOL,smartSeqHOL,seqCallRetHOL,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw,
    countdown,countdownBody]

private theorem countdown_sourceBodyWeight (n : Nat) :
    SimpVisits.hw (progToHOL (panSimpProg (countdown n))) = 5 := by
  rw [countdown_simp_program]
  simp [naturalCountdown,countdownBody,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw]

private theorem countdown_compiledPrograms (n : Nat) :
    compileProgDeclsHOLW (compileTopExactHOL ((countdownSimpFunctions n).map DeclHOL.function) (ofString "main")) =
      crepPrograms (naturalCountdownHOL n) := by
  rw [countdown_simpDeclarations,countdown_simp_program]
  rfl

private theorem countdown_mainName (n : Nat) :
    newMainNameHOL ((countdownSimpFunctions n).map DeclHOL.function) = entryName (naturalCountdownHOL n) := by
  rw [countdown_simpDeclarations,countdown_simp_program]
  rfl

private theorem countdownLiteral_wordWeight (n : Nat) :
    wordCodeWeight (sptFromAList (countdownOptimizedLiteral (BitVec.ofNat 64 n))) = 32 := by
  simp [countdownOptimizedLiteral,wordCodeWeight,wordControlWeight,sptFromAList,sptInsert,sptToAList,sptFoldi]

private theorem countdownLiteral_stackWeight (n : Nat) :
    stackCodeWeight (sptFromAList (countdownNativeStackCode n)) = 34 := by
  rw [countdown_nativeShape]
  simp [SteppedFlapjack.Phase6.prefixCode,SteppedFlapjack.Phase6.P,stackCodeWeight,stackControlWeight,sptFromAList,sptInsert,sptToAList,sptFoldi]
  with_unfolding_all decide

-- The compiler declarations retain the width proof synthesized for the first
-- witness; normalize it once before matching the polymorphic compiler theorem.

open Flapjack.Compiler.Encoders.Asm
private theorem countdownLiteral_bodyWeight (arch : AsmArchitecture) (n : Nat) :
  let ctxt := witnessLoopContext arch (naturalCountdownHOL n)
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  loopVisitWeight (optimiseScalar (compileHOLExact c .ln (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 := by
  simp only [witnessLoopContext,ctxtFcExact,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq,
    naturalCountdownCrepBody,compileHOLExact,compileExpHOLExact,compileExpsHOLExact,
    genTemps,List.length_cons,List.length_nil,List.range_succ,List.range_zero,List.map_cons,List.map_nil,
    List.append_nil,List.nil_append,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
  simp [optimiseScalar, scalarDepth, shrinkScalar, scalarFixedpoint, shrinkBranch,
    markAllHOL, loopVisitWeight, varsOfExpHOL, varsOfExpListHOL, loopNestedSeqHOL, FUPDATE_HOL,
    HolFiniteMapExact.updateEq, HolFiniteMapExact.empty, sptInsert, sptUnion, sptInter, sptSize, sptLookup, sptListInsert, sptDelete, sptOel, sptMkBN]
private theorem countdownLiteral_loopWeight (n : Nat) (source : CrepSemHOLState 64 Unit) :
  loopCodeWeight (concreteDeclLoopState riscvConfig.isa source (crepPrograms (naturalCountdownHOL n))).code = 52 := by
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n)))) = 52
  rw [natural_countdown_crep_code]
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n)))) = 52
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n) (naturalCountdown_scalar n),
    twoLoops_exact riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n)))]
  have callee : loopVisitWeight (twoCallee riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n)) = 52 := by
    have h := countdownLiteral_bodyWeight riscvConfig.isa n
    simpa [witnessLoopContext,natural_countdown_crep_code,ctxtFcExact,mkCtxtExact,makeVmapExact,twoCallee,phase3CountdownCrepBody,twoPrograms,HolFiniteMapExact.updateListEq,HolFiniteMapExact.updateList,FUPDATE_LIST,FUPDATE_LIST_HOL] using h
  simp [loopCodeWeight,sptFromAList,sptInsert,sptToAList,sptFoldi,branchingLoopEntry,loopVisitWeight,callee]


private theorem countdownLiteral_compiledLoopWeight (n : Nat) :
    loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
      (twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (naturalCountdownCrepBody (BitVec.ofNat 64 n))))) = 52 := by
  have h := countdownLiteral_loopWeight n (concreteDeclCrepState (countdownSource n) [])
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n)))) = 52 at h
  rw [countdownLiteral_programs] at h
  exact h

set_option linter.auxLemma false in
private theorem witnessWidthProof : comparisonHOLFunctions._proof_1 = @Nat.instNeZeroSucc 63 :=
  Subsingleton.elim _ _

open SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem countdown_ticks_numeric (n : Nat) : countdownTicks n =
    44195828396580057600 * (6*n+9) + 59847410146165518348 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  have sourceClock : (countdownSource n).clock = 6*n+9 := by rfl
  unfold countdownTicks callPipelineTicks
  dsimp only
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  rw [← countdownOptimized, ← countdownNative, countdownNative_bitmap, countdownNative_literal]
  have factor := countdown_nativeFactor n (fixtureCompilerConfig (countdownNativeStackCode n))
  change costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
    (sptFromAList (code1 countdownRiscVBackend.dataConf (countdownNativeStackCode n))) [4]
    (fun _ => (fixtureCompilerConfig (countdownNativeStackCode n),[],[])) = 1950 at factor
  rw [factor, uniform, init, countdownOptimized_literal, countdownLiteral_wordWeight, countdownLiteral_stackWeight]
  rw [countdown_compiledPrograms, countdown_mainName, countdownLiteral_programs]
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
  rw [entryOptimizedWeight, entrySyntaxWeight, countdownLiteral_rate, countdownLiteral_sourceCodeWeight,
    countdown_sourceTableWeight, countdown_sourceBodyWeight]
  simp only [concreteDeclLoopState, concreteDeclCrepState, noGlobalsLoweredPreCall]
  rw [countdownLiteral_compiledLoopWeight, sourceClock]
  simp [CrepSteps.statementWeight, flattenStepFactor]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
/-- The countdown reaches the initialized machine through the call-aware theorem. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      ((countdownHOLFunctions n).map DeclHOL.function) = some (fixtureCodeBytes (countdownNative n).2.2.2,(countdownNative n).1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (countdownNative n).2.2.2)) sourceFfi
      (44195828396580057600 * (6*n+9) + 59847410146165518348)
      (configuredMachineState (countdownNative n).2.2.2 (countdownNative n).1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        ((countdownHOLFunctions n).map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  let _ : DecidablePred (countdownSource n).memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have shape : ScalarSupported (countdown n) := (countdown_supported n).toScalarSupported
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
  · rw [← countdown_ticks_numeric n]
    dsimp only [countdownTicks,countdownNative,countdownOptimized]
    rw [witnessWidthProof]
    exact machineRun
  · simpa [countdownSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

def naturalCountdownSourceFunctions (n : Nat) : List (FunDeclOf 64) := [⟨"main",false,false,[],naturalCountdown n,.one⟩]
private def naturalCountdownProduction (n : Nat) := functionSourceProduction (naturalCountdownSourceFunctions n) 1 (6*n+7)
def naturalCountdownSource (n : Nat) := functionSourceExact (naturalCountdownSourceFunctions n) 1 (6*n+7)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem naturalCountdown_countedRun (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ result, evalPanValueFfiProgSteps context primitive handler (naturalCountdownProduction n).structs (countedFunctionsOfCode (naturalCountdownProduction n).code)
      (naturalCountdownProduction n).baseAddress (naturalCountdownProduction n).topAddress panSemBitVec64BytesInWord (n+3) (naturalCountdownProduction n).locals (naturalCountdownProduction n).globals (naturalCountdownProduction n).memory (naturalCountdownProduction n).ffi (naturalCountdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (naturalCountdownProduction n)))
      (contracts := some (countedContractsOfCode (naturalCountdownProduction n).code [])) = some (result,6*n+7) ∧
      result = .returned (restorePanValueLocal (fun _ => none) "x" ((naturalCountdownProduction n).locals "x"))
        (naturalCountdownProduction n).globals (naturalCountdownProduction n).memory (naturalCountdownProduction n).ffi [.word 0] := by
  let _ : DecidablePred (naturalCountdownSource n).memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have rel := functionSource_related (naturalCountdownSourceFunctions n) 1 (6*n+7) (by
    intro f hf; simp [naturalCountdownSourceFunctions] at hf; subst f; simp [NameRanged])
  have ranged : PanSemStateRelExecRanged (naturalCountdownProduction n) := by
    simp [PanSemStateRelExecRanged,naturalCountdownProduction,functionSourceProduction,sourceProduction,StructContextByteRanged,StructContext.toHOL]
  have h := counted_decl_countdown_simplified n (naturalCountdownProduction n) (naturalCountdownSource n) rel ranged "x" countdown_name_ranged range (by simp [naturalCountdownSource,functionSourceExact]; omega)
    0 context primitive handler
    (countedFunctionsOfCode (naturalCountdownProduction n).code) 0
  obtain ⟨result,final,run,hol,bound,ret⟩ := h
  refine ⟨result,?_,ret⟩
  rw [supported_calls_irrel context primitive handler (naturalCountdownProduction n).structs (countedFunctionsOfCode (naturalCountdownProduction n).code) (countedFunctionsOfCode (naturalCountdownProduction n).code)
    (naturalCountdownProduction n).baseAddress (naturalCountdownProduction n).topAddress panSemBitVec64BytesInWord (n+3)
    (some (panSemBitVec64MemoryAccess (naturalCountdownProduction n))) (some (countedContractsOfCode (naturalCountdownProduction n).code [])) [] (naturalCountdown n) (naturalCountdown_supported n).1]
  simpa [naturalCountdown] using run

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
def naturalCountdownHOLFunctions (n : Nat) := (naturalCountdownSourceFunctions n).map funDeclToHOL
def naturalCountdownSimpFunctions (n : Nat) := (naturalCountdownHOLFunctions n).map (fun f => {f with body := panSimpCompileHOL f.body})
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem naturalCountdown_noInline (n : Nat) : (functionsHOL ((compileTopExactHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  simp [naturalCountdownSimpFunctions,naturalCountdownHOLFunctions,naturalCountdownSourceFunctions,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,naturalCountdown,countdownBody,compileTopExactHOL,functionsHOL,
    compileTopFunctionLookup_eq_lookup,List.lookup,resortDeclsHOL,newMainNameHOL,isNameHOL,isDeclHOL,
    isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,
    compileExpExactHOL,inlinableHOL,functionsHOL]
private theorem naturalCountdown_simpDeclarations (n : Nat) : (naturalCountdownSimpFunctions n).map DeclHOL.function = declarations (progToHOL (panSimpProg (naturalCountdown n))) := by
  have hs : panSimpProg (naturalCountdown n) = naturalCountdown n := by
    simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]
  rw [hs]
  simp [naturalCountdownSimpFunctions,naturalCountdownHOLFunctions,naturalCountdownSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,naturalCountdown,countdownBody]
private theorem naturalCountdown_wordsGeneral (n : Nat) : supportedWordPrograms (naturalCountdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  have hs : panSimpProg (naturalCountdown n) = naturalCountdown n := by
    simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]
  rw [hs]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl
private def naturalCountdownRaw (n : Nat) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function) (ofString "main"))))
private theorem naturalCountdown_rawEq (n : Nat) : naturalCountdownRaw n = supportedWordPrograms (naturalCountdown n) := by
  simp only [naturalCountdownRaw,naturalCountdown_simpDeclarations,supportedWordPrograms,crepPrograms]
private theorem naturalCountdown_nativeRawEq (n : Nat) : compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (naturalCountdownRaw n)).2 = supportedNative (naturalCountdown n) := by
  rw [naturalCountdown_rawEq n]
  rfl
private theorem naturalCountdown_nativeCodeGeneral (n : Nat) : (supportedNative (naturalCountdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,naturalCountdown_wordsGeneral,countdownNativeStackCode]

open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable SteppedFlapjack.WordToStackSteps
noncomputable def naturalCountdownTicks (n : Nat) : Nat :=
  let entries := functionsHOL ((naturalCountdownHOLFunctions n).map DeclHOL.function)
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function)).reverse
  let decls := (naturalCountdownSimpFunctions n).map DeclHOL.function
  let lowered := compileTopExactHOL decls (ofString "main")
  let renamed := {(naturalCountdownSource n) with code := fpermCodeHOL (ofString "main") (newMainNameHOL decls) targetCode}
  let before := noGlobalsLoweredPreCall renamed (HolFiniteMapExact.empty.updateList (functionsHOL lowered).reverse)
  let panCtxt := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL lowered)) 0 (getEidsFromDeclsHOL lowered)
  let p : ProgHOL 64 := .seq .skip (.call none (newMainNameHOL decls) [])
  let programs := compileProgDeclsHOLW lowered
  let crep := compileProgExactHOLW panCtxt p
  let naturalCountdownRaw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa programs)
  let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig naturalCountdownRaw).2
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
    (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg (naturalCountdown n))))
    (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
    factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
    (max 1 (stackCodeWeight (sptFromAList code))) (6*n+7)
def naturalCountdownOptimized (n : Nat) := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function) (ofString "main")))))).2
def naturalCountdownNative (n : Nat) := compileNative riscvConfig false (naturalCountdownOptimized n)

private theorem naturalCountdownOptimized_literal (n : Nat) :
    naturalCountdownOptimized n = countdownOptimizedLiteral (BitVec.ofNat 64 n) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  unfold naturalCountdownOptimized
  change (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (naturalCountdownRaw n)).2 = _
  rw [naturalCountdown_rawEq, naturalCountdown_wordsGeneral, compileWith_eq_compile _ allocator, phase3WordConfig_eq,
    countdown_optimized_literal]

private theorem naturalCountdownNative_literal (n : Nat) : (naturalCountdownNative n).2.2.2 = countdownNativeStackCode n := by
  unfold naturalCountdownNative countdownNativeStackCode
  rw [naturalCountdownOptimized_literal, countdown_optimized_literal]

private theorem naturalCountdownNative_bitmap (n : Nat) : (naturalCountdownNative n).1 = [4] := by
  unfold naturalCountdownNative naturalCountdownOptimized
  change (compileNative riscvConfig false (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (naturalCountdownRaw n)).2).1 = _
  rw [naturalCountdown_nativeRawEq, supported_native_bitmap (naturalCountdown n) (naturalCountdown_supported n)]

private theorem naturalCountdown_sourceTableWeight (n : Nat) :
    SimpVisits.simpTableFactor (functionsHOL ((naturalCountdownHOLFunctions n).map DeclHOL.function)) = 6 := by
  simp [naturalCountdownHOLFunctions,naturalCountdownSourceFunctions,funDeclToHOL,functionsHOL,SimpVisits.simpTableFactor,
    panSimpCompileHOL,seqAssocHOL,retToTailHOL,smartSeqHOL,seqCallRetHOL,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw,
    naturalCountdown,countdownBody]

private theorem naturalCountdown_simpFixed (n : Nat) : panSimpProg (naturalCountdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]

private theorem naturalCountdown_sourceBodyWeight (n : Nat) :
    SimpVisits.hw (progToHOL (panSimpProg (naturalCountdown n))) = 5 := by
  rw [naturalCountdown_simpFixed]
  simp [naturalCountdown,countdownBody,progToHOL,expToHOL,shapeToHOL,SimpVisits.hw]

private theorem naturalCountdown_compiledPrograms (n : Nat) :
    compileProgDeclsHOLW (compileTopExactHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function) (ofString "main")) =
      crepPrograms (naturalCountdownHOL n) := by
  rw [naturalCountdown_simpDeclarations,naturalCountdown_simpFixed]
  rfl

private theorem naturalCountdown_mainName (n : Nat) :
    newMainNameHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function) = entryName (naturalCountdownHOL n) := by
  rw [naturalCountdown_simpDeclarations,naturalCountdown_simpFixed]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem naturalCountdown_ticks_numeric (n : Nat) : naturalCountdownTicks n =
    44195828396580057600 * (6*n+7) + 59847410146165518348 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  have sourceClock : (naturalCountdownSource n).clock = 6*n+7 := by rfl
  unfold naturalCountdownTicks callPipelineTicks
  dsimp only
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  rw [← naturalCountdownOptimized, ← naturalCountdownNative, naturalCountdownNative_bitmap, naturalCountdownNative_literal]
  have factor := countdown_nativeFactor n (fixtureCompilerConfig (countdownNativeStackCode n))
  change costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
    (sptFromAList (code1 countdownRiscVBackend.dataConf (countdownNativeStackCode n))) [4]
    (fun _ => (fixtureCompilerConfig (countdownNativeStackCode n),[],[])) = 1950 at factor
  rw [factor, uniform, init, naturalCountdownOptimized_literal, countdownLiteral_wordWeight, countdownLiteral_stackWeight]
  rw [naturalCountdown_compiledPrograms, naturalCountdown_mainName, countdownLiteral_programs]
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
  rw [entryOptimizedWeight, entrySyntaxWeight, countdownLiteral_rate, countdownLiteral_sourceCodeWeight,
    naturalCountdown_sourceTableWeight, naturalCountdown_sourceBodyWeight]
  simp only [concreteDeclLoopState, concreteDeclCrepState, noGlobalsLoweredPreCall]
  rw [countdownLiteral_compiledLoopWeight, sourceClock]
  simp [CrepSteps.statementWeight, flattenStepFactor]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
/-- The natural countdown reaches the initialized machine through the call-aware theorem. -/
theorem naturalCountdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      ((naturalCountdownHOLFunctions n).map DeclHOL.function) = some (fixtureCodeBytes (naturalCountdownNative n).2.2.2,(naturalCountdownNative n).1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (naturalCountdownNative n).2.2.2)) sourceFfi
      (44195828396580057600 * (6*n+9) + 59847410146165518348)
      (configuredMachineState (naturalCountdownNative n).2.2.2 (naturalCountdownNative n).1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        ((naturalCountdownHOLFunctions n).map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  let _ : DecidablePred (naturalCountdownSource n).memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have shape : ScalarSupported (naturalCountdown n) := (naturalCountdown_supported n).toScalarSupported
  have table : FunctionTableSupported (naturalCountdownSourceFunctions n) := by
    intro f hf
    simp only [naturalCountdownSourceFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
    subst f
    refine ⟨?_,shape.1,?_,rfl⟩
    · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,shape.2]
    · simp
  have unique : ((functionsHOL ((naturalCountdownHOLFunctions n).map DeclHOL.function)).map Prod.fst).Nodup := by
    simp [naturalCountdownHOLFunctions,naturalCountdownSourceFunctions,funDeclToHOL,functionsHOL]
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL ((naturalCountdownSimpFunctions n).map DeclHOL.function)).reverse
  obtain ⟨result,sourceRun,ret⟩ := naturalCountdown_countedRun n range (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  rw [ret] at sourceRun
  have span := countedCalls_initializedMachine shape (naturalCountdownProduction n) (naturalCountdownSource n) (naturalCountdownSourceFunctions n) 1 (6*n+7) table rfl rfl targetCode
    (functionsHOL ((naturalCountdownHOLFunctions n).map DeclHOL.function)) (by rfl)
    (naturalCountdownHOLFunctions n) rfl unique (naturalCountdownSimpFunctions n) rfl (ofString "main") rfl rfl
    (by simp [naturalCountdownSource,functionSourceExact,naturalCountdownSourceFunctions,funDeclToHOL,shapeToHOL,functionsHOL,
      HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,ofString])
    (naturalCountdown_noInline n) (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] (n+3) (6*n+7)
    _ _ _ _ 0 sourceRun (by rfl)
    (by
      dsimp only
      rw [← naturalCountdownRaw, naturalCountdown_nativeRawEq n, supported_native_bitmap (naturalCountdown n) (naturalCountdown_supported n)]
      decide)
    (by
      dsimp only
      rw [← naturalCountdownRaw, naturalCountdown_nativeRawEq n, naturalCountdown_nativeCodeGeneral n]
      exact countdown_stackSafe n)
    (by
      dsimp only
      rw [← naturalCountdownRaw, naturalCountdown_nativeRawEq n, naturalCountdown_nativeCodeGeneral n]
      exact countdown_compiler_facts n)
    (by
      dsimp only
      rw [← naturalCountdownRaw, naturalCountdown_rawEq n, ← supportedAllocated, supportedAllocated_eq, naturalCountdown_wordsGeneral]
      exact countdown_capacity n)
    (by
      dsimp only
      rw [← naturalCountdownRaw, naturalCountdown_nativeRawEq n, supported_native_bitmap (naturalCountdown n) (naturalCountdown_supported n)]
      rfl)
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiled,sourceResult,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [naturalCountdownProduction,functionSourceProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compilerFinal,?_,machine,ffi,?_,outputEvents,?_⟩
  · unfold naturalCountdownNative naturalCountdownOptimized
    rw [witnessWidthProof]
    exact compiled
  · have exactRun : evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (naturalCountdownNative n).2.2.2)) sourceFfi
        (naturalCountdownTicks n) (configuredMachineState (naturalCountdownNative n).2.2.2 (naturalCountdownNative n).1) =
          (.halt .success,machine,ffi) := by
      dsimp only [naturalCountdownTicks,naturalCountdownNative,naturalCountdownOptimized]
      rw [witnessWidthProof]
      exact machineRun
    rw [naturalCountdown_ticks_numeric] at exactRun
    have padded := evaluateTargetAddClock (fixtureMachineConfig (fixtureCodeStart (naturalCountdownNative n).2.2.2)) sourceFfi
      (44195828396580057600 * (6*n+7) + 59847410146165518348)
      (configuredMachineState (naturalCountdownNative n).2.2.2 (naturalCountdownNative n).1)
      (2*44195828396580057600) (.halt .success) machine ffi exactRun (by simp)
    have clockEq : 44195828396580057600 * (6*n+7) + 59847410146165518348 + 2*44195828396580057600 =
        44195828396580057600 * (6*n+9) + 59847410146165518348 := by ring
    rw [clockEq] at padded
    exact padded
  · simpa [naturalCountdownSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

end SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def comparisonCanonical := globalEntryProduction (singletonPost 1 6) (singletonEntries branching)
private theorem comparisonCanonicalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) comparisonCanonical.structs (countedFunctionsOfCode comparisonCanonical.code)
    comparisonCanonical.baseAddress comparisonCanonical.topAddress panSemBitVec64BytesInWord 2
    comparisonCanonical.locals comparisonCanonical.globals comparisonCanonical.memory comparisonCanonical.ffi (panSimpProg branching)
    (memoryAccess := some (panSemBitVec64MemoryAccess comparisonCanonical))
    (contracts := some (countedContractsOfCode comparisonCanonical.code [])) =
      some (.returned comparisonCanonical.locals comparisonCanonical.globals comparisonCanonical.memory comparisonCanonical.ffi [.word 7],6) := by
  rw [branching_simp_program]
  with_unfolding_all rfl
private theorem comparisonCap : singletonCapacity (supportedAllocated branching).2 := by
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
  all_goals with_unfolding_all decide
private theorem comparisonUnified_machine : ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit), ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram branching) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram branching)),globalSourceBitmaps (singletonSourceProgram branching),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram branching)))) sourceFfi
      (singletonTicks branching 1 6) (configuredMachineState (globalSourceCode (singletonSourceProgram branching)) (globalSourceBitmaps (singletonSourceProgram branching))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel comparisonCanonical.ffi sourceFinal.ffi := by
  apply singleton_counted_machine branching branching_supported 1 6 (by rw [singleton_bitmap branching branching_supported]; rfl)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 2 6
    comparisonCanonical.locals comparisonCanonical.globals comparisonCanonical.memory comparisonCanonical.ffi 7 comparisonCanonicalRun (by decide)
  · rw [singleton_bitmap branching branching_supported]
    decide
  · apply singleton_safe branching branching_supported
    rw [comparison_nativeCode]
    exact comparison_stackSafe
  · apply singleton_facts branching branching_supported
    rw [comparison_nativeCode]
    exact comparison_compiler_facts
  · exact singleton_capacity branching branching_supported comparisonCap
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem cmpUnifiedOptOfWeights (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (limit : Nat) (c : CrepToLoopContextExact) (entry : MlS)
    (body : compileProgExactHOLW panCtxt p = .seq .skip (.call none entry []))
    (sourceLimit : limit = 9) (crepClock : crep.clock = 7)
    (cw : CrepSteps.codeWeight programs = 3)
    (lw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 46)
    (cf : callClockFactor c (programs.map (fun row => (row.2.1,row.2.2))) 7 (.seq .skip (.call none entry [])) = 192)
    (sw : callSyntaxCost c (.seq .skip (.call none entry []) : CrepProgHOL 64) = 5)
    (ow : loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none entry []) : CrepProgHOL 64))) = 10) :
    loweredProgramOptLimit panCtxt p crep programs limit c c .ln = 24805354 := by
  unfold loweredProgramOptLimit
  dsimp only
  rw [body,sourceLimit,crepClock,cw,lw,cf,sw,ow]
  simp [CrepSteps.statementWeight]

private theorem cmpUnifiedNumericBackend (code : List (Nat × HolProg 64))
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 15 * (6*24805354+1 + ((9+1)*(6*24805354+1)+1))) = 2587607680003341948 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
private theorem cmpUnifiedNumericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 24805354) (wordEq : ww = 9) (stackEq : sw = 15)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 2587607680003341948 := by
  subst bs; subst opt; subst ww; subst sw
  exact cmpUnifiedNumericBackend code factor
private theorem cmpUnifiedNumericTicks (source : List (DeclHOL 64)) (clock : Nat) (decs : List (DeclHOL 64))
    (after : PanSemStateFiniteExact 64 Unit) (inits : List (ProgHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (entry : MlS)
    (panContext : PanToCrepContextExact 64)
    (bitmap : globalSourceBitmaps source = [4])
    (optEq : let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
      loweredProgramOptLimit panContext (.seq (nestedSeqHOL inits) (.call none entry [])) (globalEntryCrep source clock globalContext functions)
        (globalSourcePrograms source) (2*decs.length+(callEntryStateHOLFinite (installSourceFunctions after functions) HolFiniteMapExact.empty).clock+3)
        context context .ln = 24805354)
    (wordEq : wordCodeWeight (sptFromAList (globalSourceWords source)) = 9)
    (stackEq : stackCodeWeight (sptFromAList (globalSourceCode source)) = 15)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode source))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode source))) = 1950) :
    initializedGlobalTicks source clock decs after inits globalContext functions entry panContext = 2587607680003341948 := by
  unfold initializedGlobalTicks
  dsimp only
  exact cmpUnifiedNumericFromInputs _ _ _ _ _ bitmap optEq wordEq stackEq factor


private theorem cmpUnifiedPrograms : globalSourcePrograms (singletonSourceProgram branching) =
    twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody := by
  rw [singleton_programs branching branching_supported,branching_simp_program,← branching_hol_eq,branching_crep_code]
  rfl
private theorem cmpUnifiedName : singletonName branching = entryName branchingHOL := by
  simp [singletonName,branching_simp_program,branching_hol_eq]
private theorem cmpUnifiedOpt :
    let source := singletonSourceProgram branching
    let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
    loweredProgramOptLimit (globalCompilerContext source) (.seq (nestedSeqHOL []) (.call none (singletonName branching) []))
      (globalEntryCrep source 6 singletonGlobals (singletonEntries branching)) (globalSourcePrograms source)
      (2*(([] : List (DeclHOL 64)).length)+(callEntryStateHOLFinite (installSourceFunctions (singletonPost 1 6) (singletonEntries branching)) HolFiniteMapExact.empty).clock+3)
      context context .ln = 24805354 := by
  dsimp only
  apply cmpUnifiedOptOfWeights _ _ _ _ _ _ (singletonName branching)
  · simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
  · rfl
  · rfl
  · rw [cmpUnifiedPrograms]; exact cmpCodeWeight _
  · rw [cmpUnifiedPrograms]; exact cmpLoopWeightRaw
  · rw [cmpUnifiedPrograms,cmpUnifiedName]; exact cmpRate _ _ _
  · exact entrySyntaxWeight _ _
  · exact entryOptimizedWeight _ _
private theorem cmpUnifiedWordWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : wordCodeWeight (sptFromAList (supportedAllocated p).2) = 9) :
    wordCodeWeight (sptFromAList (globalSourceWords (singletonSourceProgram p))) = 9 := by
  rw [singleton_words p h]; exact w
private theorem cmpUnifiedStackWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : stackCodeWeight (sptFromAList (supportedNative p).2.2.2) = 15) :
    stackCodeWeight (sptFromAList (globalSourceCode (singletonSourceProgram p))) = 15 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact w
private theorem cmpUnifiedFactor (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative p).2.2.2)) [4]
      (fixtureStackOracle (fixtureCompilerConfig (supportedNative p).2.2.2)) = 1950) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode (singletonSourceProgram p)))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode (singletonSourceProgram p)))) = 1950 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact factor
private theorem cmpUnifiedClock : singletonTicks branching 1 6 = 2587607680003341948 := by
  apply cmpUnifiedNumericTicks _ _ _ _ _ _ _ _ _ (singleton_bitmap branching branching_supported) cmpUnifiedOpt
  · apply cmpUnifiedWordWeight branching branching_supported
    rw [← cmpOpt]; exact cmpWordWeight
  · apply cmpUnifiedStackWeight branching branching_supported
    rw [← sameNative]; exact cmpStackWeight
  · apply cmpUnifiedFactor branching branching_supported
    rw [← sameNative]; exact cmpFactor _


private theorem cmpUnifiedSource : PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
    (singletonSourceProgram branching) = .terminate .success sourceFfi.ioEvents := by
  obtain ⟨final,_,behavior,ffiRel⟩ := singleton_source_semantics branching branching_supported 1 6
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 2 6
    comparisonProduction.locals comparisonProduction.globals comparisonProduction.memory comparisonProduction.ffi 7
    (comparison_sourceRun _ _ _) (by decide)
  have events : final.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] final.ffi.ioEvents at h
    cases heq : final.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  simpa [sourceTemplateFor_one,sourceFfi,events] using behavior
/-- The comparison source reaches the initialized machine at a concrete clock. -/
theorem comparisonFixture_machine : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram branching) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram branching)),globalSourceBitmaps (singletonSourceProgram branching),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram branching)))) sourceFfi
      2587607680003341948 (configuredMachineState (globalSourceCode (singletonSourceProgram branching)) (globalSourceBitmaps (singletonSourceProgram branching))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
    PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (singletonSourceProgram branching) = .terminate .success finalFfi.ioEvents := by
  obtain ⟨sourceFinal,machine,ffi,compiler,compiled,run,events,ffiRel⟩ := comparisonUnified_machine
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] sourceFinal.ffi.ioEvents at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have machineEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compiler,machine,ffi,compiled,?_,machineEvents,?_⟩
  · simpa only [← cmpUnifiedClock] using run
  · rw [machineEvents]; exact cmpUnifiedSource

end SteppedFlapjack.Concrete
