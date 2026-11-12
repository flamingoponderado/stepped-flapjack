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
private theorem branchingLoop_simpDeclarations : branchingLoopSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg branchingLoop)) := by
  rw [branchingLoop_simp_program]
  simp [branchingLoopSimpFunctions,branchingLoopHOLFunctions,branchingLoopSourceFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,branchingLoop]
private theorem branchingLoop_nativeCode : (supportedNative branchingLoop).2.2.2 = branchingLoopNativeCode := by
  have words : supportedWordPrograms branchingLoop = branchWordPrograms := by
    unfold supportedWordPrograms
    rw [branchingLoop_simp_program,branchingLoop_crep_code]
    rfl
  simp only [supportedNative,supportedAllocated_eq,words,branchingLoopNativeCode]
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
private theorem brcFactor (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf branchingLoopNative.2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [branchSameCode]
  unfold branchingLoopNativeCode
  rw [branch_optimized_table,riscvNative_two_entry_code]
  decide +kernel

open Flapjack.Basis.Pure.MlString
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
private theorem brcLoopWeightRaw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    ([(ofString "main",[],.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])),
      (entryName (progToHOL branchingLoop),[],branchingLoopCrepBody)] : List (MlString × List Nat × CrepProgHOL 64)))) = 80 := by
  change loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    (twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody))) = 80
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody branchingLoop_scalar,
    twoLoops_exact riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop)))]
  with_unfolding_all decide


end

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

def countdownOptimized (n : Nat) := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
  (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL ((countdownSimpFunctions n).map DeclHOL.function) (ofString "main")))))).2

private theorem countdownOptimized_literal (n : Nat) :
    countdownOptimized n = countdownOptimizedLiteral (BitVec.ofNat 64 n) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  unfold countdownOptimized
  change (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (countdownRaw n)).2 = _
  rw [countdown_rawEq, countdown_wordsGeneral, compileWith_eq_compile _ allocator, phase3WordConfig_eq,
    countdown_optimized_literal]

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

open SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove

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

private theorem naturalCountdown_simpFixed (n : Nat) : panSimpProg (naturalCountdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]

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

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def loopCanonical := globalEntryProduction (singletonPost 1 23) (singletonEntries branchingLoop)
private theorem loopCanonicalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) loopCanonical.structs (countedFunctionsOfCode loopCanonical.code)
    loopCanonical.baseAddress loopCanonical.topAddress panSemBitVec64BytesInWord 7
    loopCanonical.locals loopCanonical.globals loopCanonical.memory loopCanonical.ffi (panSimpProg branchingLoop)
    (memoryAccess := some (panSemBitVec64MemoryAccess loopCanonical))
    (contracts := some (countedContractsOfCode loopCanonical.code [])) =
      some (.returned loopCanonical.locals loopCanonical.globals loopCanonical.memory loopCanonical.ffi [.word 7],23) := by
  rw [branchingLoop_simp_program]
  simp (config := {maxSteps := 1000000}) [branchingLoop,evalPanValueFfiProgSteps,panValueDecAccepted,panValueIteCondition,panValueAssignLocalResult,
    panValueReturnResult,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,
    panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,
    RiscV.panRiscVMemoryModel,RiscV.panRiscVCmp,updatePanValueMap,restorePanValueFfiLocal,
    panShapeMatches,panValueShape,panValueAssignmentValid]
  funext name
  simp [restorePanValueLocal,loopCanonical,globalEntryProduction,panSemExecStateOfHOLWithKeys,globalEntrySource,installSourceFunctions,callEntryStateHOLFinite,panSemStateOfExactWithKeys,HolFiniteMapExact.empty]
private theorem loopCap : singletonCapacity (supportedAllocated branchingLoop).2 := by
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
  all_goals with_unfolding_all decide
private theorem loopUnified_machine : ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit), ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram branchingLoop) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram branchingLoop)),globalSourceBitmaps (singletonSourceProgram branchingLoop),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram branchingLoop)))) sourceFfi
      (singletonTicks branchingLoop 1 23) (configuredMachineState (globalSourceCode (singletonSourceProgram branchingLoop)) (globalSourceBitmaps (singletonSourceProgram branchingLoop))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel loopCanonical.ffi sourceFinal.ffi := by
  apply singleton_counted_machine branchingLoop branchingLoop_supported 1 23 (by rw [singleton_bitmap branchingLoop branchingLoop_supported]; rfl)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 7 23
    loopCanonical.locals loopCanonical.globals loopCanonical.memory loopCanonical.ffi 7 loopCanonicalRun (by decide)
  · rw [singleton_bitmap branchingLoop branchingLoop_supported]
    decide
  · apply singleton_safe branchingLoop branchingLoop_supported
    rw [branchingLoop_nativeCode]
    exact branching_stackSafe
  · apply singleton_facts branchingLoop branchingLoop_supported
    rw [branchingLoop_nativeCode]
    exact branching_compiler_facts
  · exact singleton_capacity branchingLoop branchingLoop_supported loopCap

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem brcUnifiedOptOfWeights (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (limit : Nat) (c : CrepToLoopContextExact) (entry : MlS)
    (body : compileProgExactHOLW panCtxt p = .seq .skip (.call none entry []))
    (sourceLimit : limit = 26) (crepClock : crep.clock = 24)
    (cw : CrepSteps.codeWeight programs = 11)
    (lw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 80)
    (cf : callClockFactor c (programs.map (fun row => (row.2.1,row.2.2))) 24 (.seq .skip (.call none entry [])) = 306)
    (sw : callSyntaxCost c (.seq .skip (.call none entry []) : CrepProgHOL 64) = 5)
    (ow : loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none entry []) : CrepProgHOL 64))) = 10) :
    loweredProgramOptLimit panCtxt p crep programs limit c c .ln = 1181353838 := by
  unfold loweredProgramOptLimit
  dsimp only
  rw [body,sourceLimit,crepClock,cw,lw,cf,sw,ow]
  simp [CrepSteps.statementWeight]

private theorem brcUnifiedNumericBackend (code : List (Nat × HolProg 64))
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 48 * (6*1181353838+1 + ((46+1)*(6*1181353838+1)+1))) = 1720804472507697866748 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
private theorem brcUnifiedNumericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 1181353838) (wordEq : ww = 46) (stackEq : sw = 48)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 1720804472507697866748 := by
  subst bs; subst opt; subst ww; subst sw
  exact brcUnifiedNumericBackend code factor
private theorem brcUnifiedNumericTicks (source : List (DeclHOL 64)) (clock : Nat) (decs : List (DeclHOL 64))
    (after : PanSemStateFiniteExact 64 Unit) (inits : List (ProgHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (entry : MlS)
    (panContext : PanToCrepContextExact 64)
    (bitmap : globalSourceBitmaps source = [4])
    (optEq : let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
      loweredProgramOptLimit panContext (.seq (nestedSeqHOL inits) (.call none entry [])) (globalEntryCrep source clock globalContext functions)
        (globalSourcePrograms source) (2*decs.length+(callEntryStateHOLFinite (installSourceFunctions after functions) HolFiniteMapExact.empty).clock+3)
        context context .ln = 1181353838)
    (wordEq : wordCodeWeight (sptFromAList (globalSourceWords source)) = 46)
    (stackEq : stackCodeWeight (sptFromAList (globalSourceCode source)) = 48)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode source))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode source))) = 1950) :
    initializedGlobalTicks source clock decs after inits globalContext functions entry panContext = 1720804472507697866748 := by
  unfold initializedGlobalTicks
  dsimp only
  exact brcUnifiedNumericFromInputs _ _ _ _ _ bitmap optEq wordEq stackEq factor


private theorem brcUnifiedPrograms : globalSourcePrograms (singletonSourceProgram branchingLoop) =
    twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody := by
  rw [singleton_programs branchingLoop branchingLoop_supported,branchingLoop_simp_program,branchingLoop_crep_code]
  rfl
private theorem brcUnifiedName : singletonName branchingLoop = entryName (progToHOL branchingLoop) := by
  simp [singletonName,branchingLoop_simp_program]
private theorem brcUnifiedOpt :
    let source := singletonSourceProgram branchingLoop
    let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
    loweredProgramOptLimit (globalCompilerContext source) (.seq (nestedSeqHOL []) (.call none (singletonName branchingLoop) []))
      (globalEntryCrep source 23 singletonGlobals (singletonEntries branchingLoop)) (globalSourcePrograms source)
      (2*(([] : List (DeclHOL 64)).length)+(callEntryStateHOLFinite (installSourceFunctions (singletonPost 1 23) (singletonEntries branchingLoop)) HolFiniteMapExact.empty).clock+3)
      context context .ln = 1181353838 := by
  dsimp only
  apply brcUnifiedOptOfWeights _ _ _ _ _ _ (singletonName branchingLoop)
  · simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
  · rfl
  · rfl
  · rw [brcUnifiedPrograms]; exact brcCodeWeight _
  · rw [brcUnifiedPrograms]; exact brcLoopWeightRaw
  · rw [brcUnifiedPrograms,brcUnifiedName]; exact brcRate _ _ _
  · exact entrySyntaxWeight _ _
  · exact entryOptimizedWeight _ _
private theorem brcUnifiedWordWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : wordCodeWeight (sptFromAList (supportedAllocated p).2) = 46) :
    wordCodeWeight (sptFromAList (globalSourceWords (singletonSourceProgram p))) = 46 := by
  rw [singleton_words p h]; exact w
private theorem brcUnifiedStackWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : stackCodeWeight (sptFromAList (supportedNative p).2.2.2) = 48) :
    stackCodeWeight (sptFromAList (globalSourceCode (singletonSourceProgram p))) = 48 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact w
private theorem brcUnifiedFactor (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative p).2.2.2)) [4]
      (fixtureStackOracle (fixtureCompilerConfig (supportedNative p).2.2.2)) = 1950) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode (singletonSourceProgram p)))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode (singletonSourceProgram p)))) = 1950 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact factor
private theorem brcUnifiedClock : singletonTicks branchingLoop 1 23 = 1720804472507697866748 := by
  apply brcUnifiedNumericTicks _ _ _ _ _ _ _ _ _ (singleton_bitmap branchingLoop branchingLoop_supported) brcUnifiedOpt
  · apply brcUnifiedWordWeight branchingLoop branchingLoop_supported
    rw [← brcOpt]; exact brcWordWeight
  · apply brcUnifiedStackWeight branchingLoop branchingLoop_supported
    rw [← branchSameNative]; exact brcStackWeight
  · apply brcUnifiedFactor branchingLoop branchingLoop_supported
    rw [← branchSameNative]; exact brcFactor _


private theorem brcUnifiedSource : PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
    (singletonSourceProgram branchingLoop) = .terminate .success sourceFfi.ioEvents := by
  obtain ⟨final,_,behavior,ffiRel⟩ := singleton_source_semantics branchingLoop branchingLoop_supported 1 23
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 7 23
    branchingLoopProduction.locals branchingLoopProduction.globals branchingLoopProduction.memory branchingLoopProduction.ffi 7
    (branchingLoop_countedRun _ _ _) (by decide)
  have events : final.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] final.ffi.ioEvents at h
    cases heq : final.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  simpa [sourceTemplateFor_one,sourceFfi,events] using behavior
/-- The branching loop source reaches the initialized machine at a concrete clock. -/
theorem branchingLoopFixture_machine : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram branchingLoop) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram branchingLoop)),globalSourceBitmaps (singletonSourceProgram branchingLoop),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram branchingLoop)))) sourceFfi
      1720804472507697866748 (configuredMachineState (globalSourceCode (singletonSourceProgram branchingLoop)) (globalSourceBitmaps (singletonSourceProgram branchingLoop))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
    PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (singletonSourceProgram branchingLoop) = .terminate .success finalFfi.ioEvents := by
  obtain ⟨sourceFinal,machine,ffi,compiler,compiled,run,events,ffiRel⟩ := loopUnified_machine
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] sourceFinal.ffi.ioEvents at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have machineEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compiler,machine,ffi,compiled,?_,machineEvents,?_⟩
  · simpa only [← brcUnifiedClock] using run
  · rw [machineEvents]; exact brcUnifiedSource


end SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.LoopLiveSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def cdCanonical (n : Nat) := globalEntryProduction (singletonPost 1 (6*n+9)) (singletonEntries (countdown n))
private theorem cdCanonicalRun (n : Nat) (range : n < 2^64) :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
      (cdCanonical n).structs (countedFunctionsOfCode (cdCanonical n).code) (cdCanonical n).baseAddress (cdCanonical n).topAddress
      panSemBitVec64BytesInWord (n+3) (cdCanonical n).locals (cdCanonical n).globals (cdCanonical n).memory (cdCanonical n).ffi (panSimpProg (countdown n))
      (memoryAccess := some (panSemBitVec64MemoryAccess (cdCanonical n))) (contracts := some (countedContractsOfCode (cdCanonical n).code [])) =
      some (.returned (restorePanValueLocal (fun _ => none) "x" ((cdCanonical n).locals "x"))
        (cdCanonical n).globals (cdCanonical n).memory (cdCanonical n).ffi [.word 0],6*n+7) := by
  let source := globalEntrySource (singletonPost 1 (6*n+9)) (singletonEntries (countdown n))
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have rel := globalEntryProduction_related (singletonPost 1 (6*n+9)) (singletonEntries (countdown n)) (by rfl)
  have ranged := globalEntryProduction_ranged (singletonPost 1 (6*n+9)) (singletonEntries (countdown n))
  have h := counted_decl_countdown_simplified n (cdCanonical n) source rel ranged "x" countdown_name_ranged range (by
    simp [source,globalEntrySource,callEntryStateHOLFinite,installSourceFunctions,singletonPost]; omega)
    0 (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
    (countedFunctionsOfCode (cdCanonical n).code) 0
  obtain ⟨result,final,run,hol,bound,ret⟩ := h
  rw [countdown_simp_program]
  rw [supported_calls_irrel _ _ _ (cdCanonical n).structs (countedFunctionsOfCode (cdCanonical n).code) (countedFunctionsOfCode (cdCanonical n).code)
    (cdCanonical n).baseAddress (cdCanonical n).topAddress panSemBitVec64BytesInWord (n+3)
    (some (panSemBitVec64MemoryAccess (cdCanonical n))) (some (countedContractsOfCode (cdCanonical n).code [])) [] (naturalCountdown n) (naturalCountdown_supported n).1]
  rw [ret] at run
  simpa [naturalCountdown] using run

private theorem cdCap (n : Nat) : singletonCapacity (supportedAllocated (countdown n)).2 := by
  rw [supportedAllocated_eq,countdown_wordsGeneral]
  exact countdown_capacity n
private theorem cdUnifiedMachine (n : Nat) (range : n < 2^64) : ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit), ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram (countdown n)) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram (countdown n))),globalSourceBitmaps (singletonSourceProgram (countdown n)),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram (countdown n))))) sourceFfi
      (singletonTicks (countdown n) 1 (6*n+9)) (configuredMachineState (globalSourceCode (singletonSourceProgram (countdown n))) (globalSourceBitmaps (singletonSourceProgram (countdown n)))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel (cdCanonical n).ffi sourceFinal.ffi := by
  apply singleton_counted_machine (countdown n) (countdown_supported n) 1 (6*n+9) (by rw [singleton_bitmap _ (countdown_supported n)]; rfl)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] (n+3) (6*n+7)
    (restorePanValueLocal (fun _ => none) "x" ((cdCanonical n).locals "x")) (cdCanonical n).globals (cdCanonical n).memory (cdCanonical n).ffi 0 (cdCanonicalRun n range) (by omega)
  · rw [singleton_bitmap _ (countdown_supported n)]; decide
  · apply singleton_safe _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdown_stackSafe n
  · apply singleton_facts _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdown_compiler_facts n
  · exact singleton_capacity _ (countdown_supported n) (cdCap n)


open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem cdOptOfWeights (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (limit clock : Nat) (c : CrepToLoopContextExact) (entry : MlS)
    (body : compileProgExactHOLW panCtxt p = .seq .skip (.call none entry []))
    (sourceLimit : limit = clock+3) (crepClock : crep.clock = clock+1)
    (cw : CrepSteps.codeWeight programs = 8)
    (lw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 52)
    (cf : callClockFactor c (programs.map (fun row => (row.2.1,row.2.2))) (clock+1) (.seq .skip (.call none entry [])) = 216)
    (sw : callSyntaxCost c (.seq .skip (.call none entry []) : CrepProgHOL 64) = 5)
    (ow : loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none entry []) : CrepProgHOL 64))) = 10) :
    loweredProgramOptLimit panCtxt p crep programs limit c c .ln = 10083528*clock+31499182 := by
  unfold loweredProgramOptLimit
  dsimp only
  rw [body,sourceLimit,crepClock,cw,lw,cf,sw,ow]
  simp [CrepSteps.statementWeight]
  omega
private theorem cdNumericBackend (code : List (Nat × HolProg 64)) (clock : Nat)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 34 * (6*(10083528*clock+31499182)+1 + (33*(6*(10083528*clock+31499182)+1)+1))) =
        7369523319287001600*clock+23021105068872462348 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
  omega
private theorem cdNumericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (clock opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 10083528*clock+31499182) (wordEq : ww = 32) (stackEq : sw = 34)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 7369523319287001600*clock+23021105068872462348 := by
  subst bs; subst opt; subst ww; subst sw
  exact cdNumericBackend code clock factor
private theorem cdNumericTicks (source : List (DeclHOL 64)) (clock : Nat) (decs : List (DeclHOL 64))
    (after : PanSemStateFiniteExact 64 Unit) (inits : List (ProgHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (entry : MlS)
    (panContext : PanToCrepContextExact 64)
    (bitmap : globalSourceBitmaps source = [4])
    (optEq : let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
      loweredProgramOptLimit panContext (.seq (nestedSeqHOL inits) (.call none entry [])) (globalEntryCrep source clock globalContext functions)
        (globalSourcePrograms source) (2*decs.length+(callEntryStateHOLFinite (installSourceFunctions after functions) HolFiniteMapExact.empty).clock+3)
        context context .ln = 10083528*clock+31499182)
    (wordEq : wordCodeWeight (sptFromAList (globalSourceWords source)) = 32)
    (stackEq : stackCodeWeight (sptFromAList (globalSourceCode source)) = 34)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode source))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode source))) = 1950) :
    initializedGlobalTicks source clock decs after inits globalContext functions entry panContext = 7369523319287001600*clock+23021105068872462348 := by
  unfold initializedGlobalTicks
  dsimp only
  exact cdNumericFromInputs _ _ _ _ _ _ bitmap optEq wordEq stackEq factor


private theorem cdPrograms (n : Nat) : globalSourcePrograms (singletonSourceProgram (countdown n)) =
    twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (naturalCountdownCrepBody (BitVec.ofNat 64 n)) := by
  rw [singleton_programs _ (countdown_supported n),countdown_simp_program]
  exact countdownLiteral_programs n
private theorem cdName (n : Nat) : singletonName (countdown n) = entryName (naturalCountdownHOL n) := by
  simp [singletonName,countdown_simp_program,naturalCountdownHOL]
private theorem cdOpt (n : Nat) :
    let source := singletonSourceProgram (countdown n)
    let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
    loweredProgramOptLimit (globalCompilerContext source) (.seq (nestedSeqHOL []) (.call none (singletonName (countdown n)) []))
      (globalEntryCrep source (6*n+9) singletonGlobals (singletonEntries (countdown n))) (globalSourcePrograms source)
      (2*(([] : List (DeclHOL 64)).length)+(callEntryStateHOLFinite (installSourceFunctions (singletonPost 1 (6*n+9)) (singletonEntries (countdown n))) HolFiniteMapExact.empty).clock+3)
      context context .ln = 10083528*(6*n+9)+31499182 := by
  dsimp only
  apply cdOptOfWeights _ _ _ _ _ (6*n+9) _ (singletonName (countdown n))
  · simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
  · simp [callEntryStateHOLFinite,installSourceFunctions,singletonPost]
  · rfl
  · rw [cdPrograms]; exact countdownLiteral_sourceCodeWeight _ _
  · rw [cdPrograms]; exact countdownLiteral_compiledLoopWeight _
  · rw [cdPrograms,cdName]; exact countdownLiteral_rate _ _ _ _
  · exact entrySyntaxWeight _ _
  · exact entryOptimizedWeight _ _
private theorem cdWordWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : wordCodeWeight (sptFromAList (supportedAllocated p).2) = 32) :
    wordCodeWeight (sptFromAList (globalSourceWords (singletonSourceProgram p))) = 32 := by
  rw [singleton_words p h]; exact w
private theorem cdStackWeight (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (w : stackCodeWeight (sptFromAList (supportedNative p).2.2.2) = 34) :
    stackCodeWeight (sptFromAList (globalSourceCode (singletonSourceProgram p))) = 34 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact w
private theorem cdFactor (p : Prog (RiscV.Word 64)) (h : CallFreeSupported p)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative p).2.2.2)) [4]
      (fixtureStackOracle (fixtureCompilerConfig (supportedNative p).2.2.2)) = 1950) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode (singletonSourceProgram p)))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode (singletonSourceProgram p)))) = 1950 := by
  unfold globalSourceCode; rw [singleton_native p h]; exact factor
private theorem cdOptEq (n : Nat) : countdownOptimized n = (supportedAllocated (countdown n)).2 := by
  unfold countdownOptimized supportedAllocated
  change (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (countdownRaw n)).2 = _
  rw [countdown_rawEq]

private theorem cdClock (n : Nat) : singletonTicks (countdown n) 1 (6*n+9) =
    7369523319287001600*(6*n+9)+23021105068872462348 := by
  apply cdNumericTicks _ _ _ _ _ _ _ _ _ (singleton_bitmap _ (countdown_supported n)) (cdOpt n)
  · apply cdWordWeight _ (countdown_supported n)
    rw [← cdOptEq, countdownOptimized_literal]; exact countdownLiteral_wordWeight n
  · apply cdStackWeight _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdownLiteral_stackWeight n
  · apply cdFactor _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdown_nativeFactor n _


private theorem cdSource (n : Nat) (range : n < 2^64) : PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
    (singletonSourceProgram (countdown n)) = .terminate .success sourceFfi.ioEvents := by
  obtain ⟨result,run,ret⟩ := countdown_countedRun n range (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  rw [ret] at run
  obtain ⟨final,_,behavior,ffiRel⟩ := singleton_source_semantics (countdown n) (countdown_supported n) 1 (6*n+9)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] (n+4) (6*n+9)
    (restorePanValueLocal (fun _ => none) "x" ((countdownProduction n).locals "x")) (countdownProduction n).globals (countdownProduction n).memory (countdownProduction n).ffi 0 run (by omega)
  have events : final.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] final.ffi.ioEvents at h
    cases heq : final.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  simpa [sourceTemplateFor_one,sourceFfi,events] using behavior
/-- The countdown source reaches the initialized machine at an explicit input-dependent clock. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram (countdown n)) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram (countdown n))),globalSourceBitmaps (singletonSourceProgram (countdown n)),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram (countdown n))))) sourceFfi
      (7369523319287001600*(6*n+9)+23021105068872462348) (configuredMachineState (globalSourceCode (singletonSourceProgram (countdown n))) (globalSourceBitmaps (singletonSourceProgram (countdown n)))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
    PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (singletonSourceProgram (countdown n)) = .terminate .success finalFfi.ioEvents := by
  obtain ⟨sourceFinal,machine,ffi,compiler,compiled,run,events,ffiRel⟩ := cdUnifiedMachine n range
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] sourceFinal.ffi.ioEvents at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have machineEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compiler,machine,ffi,compiled,?_,machineEvents,?_⟩
  · simpa only [← cdClock] using run
  · rw [machineEvents]; exact cdSource n range

end SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem sameCountdownPrograms (n : Nat) : globalSourcePrograms (singletonSourceProgram (naturalCountdown n)) =
    globalSourcePrograms (singletonSourceProgram (countdown n)) := by
  rw [singleton_programs _ (naturalCountdown_supported n),singleton_programs _ (countdown_supported n),
    naturalCountdown_simpFixed,countdown_simp_program]
private theorem sameCountdownRaw (n : Nat) :
    panToWordCompileProgHOL riscvConfig.isa (singletonSourceProgram (naturalCountdown n)) = globalSourceRaw (singletonSourceProgram (countdown n)) := by
  change globalSourceRaw (singletonSourceProgram (naturalCountdown n)) = _
  unfold globalSourceRaw
  rw [sameCountdownPrograms]
private theorem natCdSource (n : Nat) (range : n < 2^64) : PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
    (singletonSourceProgram (naturalCountdown n)) = .terminate .success sourceFfi.ioEvents := by
  obtain ⟨result,run,ret⟩ := naturalCountdown_countedRun n range (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  rw [ret] at run
  obtain ⟨final,_,behavior,ffiRel⟩ := singleton_source_semantics (naturalCountdown n) (naturalCountdown_supported n) 1 (6*n+7)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] (n+3) (6*n+7)
    (restorePanValueLocal (fun _ => none) "x" ((naturalCountdownProduction n).locals "x")) (naturalCountdownProduction n).globals (naturalCountdownProduction n).memory (naturalCountdownProduction n).ffi 0 run (by omega)
  have events : final.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] final.ffi.ioEvents at h
    cases heq : final.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  simpa [sourceTemplateFor_one,sourceFfi,events] using behavior
/-- The natural countdown compiles to the same machine code as the countdown. -/
theorem naturalCountdownFixture_machine (n : Nat) (range : n < 2^64) : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig (singletonSourceProgram (naturalCountdown n)) =
      some (fixtureCodeBytes (globalSourceCode (singletonSourceProgram (countdown n))),globalSourceBitmaps (singletonSourceProgram (countdown n)),compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode (singletonSourceProgram (countdown n))))) sourceFfi
      (7369523319287001600*(6*n+9)+23021105068872462348) (configuredMachineState (globalSourceCode (singletonSourceProgram (countdown n))) (globalSourceBitmaps (singletonSourceProgram (countdown n)))) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
    PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main") (singletonSourceProgram (naturalCountdown n)) = .terminate .success finalFfi.ioEvents := by
  have safe : fixtureStackSafe (globalSourceCode (singletonSourceProgram (countdown n))) = true := by
    apply singleton_safe _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdown_stackSafe n
  have facts : (fixtureRemoveLabels (globalSourceCode (singletonSourceProgram (countdown n)))).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode (singletonSourceProgram (countdown n)))).length ≤ 0xecc ∧
      (fixtureCodeBytes (globalSourceCode (singletonSourceProgram (countdown n)))).length % 4 = 0 := by
    apply singleton_facts _ (countdown_supported n)
    rw [countdown_nativeCodeGeneral]; exact countdown_compiler_facts n
  obtain ⟨compiler,compiled⟩ := globalSource_compilerOutputFor (singletonSourceProgram (naturalCountdown n))
    (singletonSourceProgram (countdown n)) (sameCountdownRaw n) safe facts.1
  obtain ⟨_,machine,ffi,_,run,events,_⟩ := countdownFixture_machine n range
  exact ⟨compiler,machine,ffi,compiled,run,events,by rw [events]; exact natCdSource n range⟩
end SteppedFlapjack.Concrete
