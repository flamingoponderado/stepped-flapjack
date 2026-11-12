import SteppedFlapjack.Concrete.HeapWordNativeFacts

/-! The heap store/load witness through the composed source-to-machine theorem. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def heapFunctions : List (FunDeclOf 64) := [⟨"main",false,false,[],heapWordWitness,.one⟩]
private def heapProduction := functionSourceProduction heapFunctions 1 7
def heapHOLFunctions := heapFunctions.map funDeclToHOL
def heapSimpFunctions := heapHOLFunctions.map (fun f => {f with body := panSimpCompileHOL f.body})
def heapSource := functionSourceExact heapFunctions 1 7
private instance : DecidablePred heapSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance

private theorem heapSource_run :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
      heapProduction.structs (countedFunctionsOfCode heapProduction.code) heapProduction.baseAddress heapProduction.topAddress
      panSemBitVec64BytesInWord 10 heapProduction.locals heapProduction.globals heapProduction.memory heapProduction.ffi heapWordWitness
      (memoryAccess := some (panSemBitVec64MemoryAccess heapProduction))
      (contracts := some (countedContractsOfCode heapProduction.code [])) =
      some (.returned heapProduction.locals heapProduction.globals (updatePanValueMemory heapProduction.memory 0xa1000100 (.word 7)) heapProduction.ffi [.word 7],7) := by
  have hs : SupportedIn [] heapWordWitness := .seq (.store (.const _) (.const _)) (.ret (.load (.const _)))
  rw [supported_calls_irrel _ _ _ heapProduction.structs (countedFunctionsOfCode heapProduction.code) [] heapProduction.baseAddress heapProduction.topAddress
    panSemBitVec64BytesInWord 10 (some (panSemBitVec64MemoryAccess heapProduction))
    (some (countedContractsOfCode heapProduction.code [])) [] heapWordWitness hs]
  simpa [panSemBitVec64BytesInWord,heapProduction,functionSourceProduction,sourceProduction,initialWordFor_one,
    executableState,singleEntrySourceProduction,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,
    panSemBitVec64WordModel,panSemWordModel,RiscV.panRiscVMemoryModel] using heapWordWitness_run



private theorem heap_simpDeclarations : heapSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg heapWordWitness)) := by
  simp [heapSimpFunctions,heapHOLFunctions,heapFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,heapWordWitness,panSimpProg,seqAssoc,retToTail,smartSeq,seqCallRet]


private theorem heap_noInline : (functionsHOL ((compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  rw [heap_simpDeclarations]
  exact singleEntry_inline_selection_empty _ _


open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps
noncomputable def heapTicks : Nat :=
  let entries := functionsHOL (heapHOLFunctions.map DeclHOL.function)
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (heapSimpFunctions.map DeclHOL.function)).reverse
  let decls := heapSimpFunctions.map DeclHOL.function
  let lowered := compileTopExactHOL decls (ofString "main")
  let renamed := {heapSource with code := fpermCodeHOL (ofString "main") (newMainNameHOL decls) targetCode}
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
    (SimpVisits.simpTableFactor entries) (SimpVisits.hw (progToHOL (panSimpProg heapWordWitness)))
    (callClockFactor ctxt rows initial.clock crep) initial.clock (callSyntaxCost ctxt crep)
    factor (loopVisitWeight opt) optFactor (max 1 (wordCodeWeight (sptFromAList optimized)))
    (max 1 (stackCodeWeight (sptFromAList code))) 7

private theorem heapFound : heapSource.code.lookup (ofString "main") = some ([],progToHOL heapWordWitness,.one) := by
  simp [heapSource,functionSourceExact,heapFunctions,funDeclToHOL,shapeToHOL,functionsHOL,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,ofString]


private theorem heapRaw_same : loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))) =
    supportedWordPrograms heapWordWitness := by
  unfold supportedWordPrograms crepPrograms
  rw [heap_simpDeclarations]



private theorem heapAllocator_same : compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
    (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
      (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))))) =
    supportedAllocated heapWordWitness := by
  exact congrArg (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig) heapRaw_same


private theorem heapNative_same :
    compileNative riscvConfig false (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
        (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2 =
    supportedNative heapWordWitness := by
  exact congrArg (fun result => compileNative riscvConfig false result.2) heapAllocator_same


private theorem heapBitmapFitRaw : 0xa0020018 + (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2).1.length*8 ≤ 0xa0410000 := by
  have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
  have bmp := (congrArg Prod.fst heapNative_same).trans (supported_native_bitmap heapWordWitness hs)
  exact (congrArg (fun bitmaps => 0xa0020018 + bitmaps.length*8 ≤ 0xa0410000) bmp).mpr (by decide)


private theorem heapSafeRaw : fixtureStackSafe (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2).2.2.2 = true := by
  exact (congrArg (fun n => fixtureStackSafe n.2.2.2 = true) heapNative_same).mpr heapNative_safe

private theorem heapFactsRaw :
  let code := (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2).2.2.2
  (fixtureRemoveLabels code).isSome = true ∧ (fixtureCodeBytes code).length ≤ 0xecc ∧
    (fixtureCodeBytes code).length % 4 = 0 := by
  have eq := congrArg (fun n => n.2.2.2) heapNative_same
  have p := congrArg (fun code => (fixtureRemoveLabels code).isSome = true ∧
    (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0) eq
  exact p.mpr heapNative_compilerFacts


open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
private def heapCapacityCondition (optimized : List (Nat × Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
  optionLe (optionMap₂ max (some (max 1 (1+frame)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172)
private theorem heapCapacityRaw : heapCapacityCondition (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2 := by
  have eq := (congrArg Prod.snd heapAllocator_same).trans heapOptimizedLiteral_eq
  exact (congrArg heapCapacityCondition eq).mpr heapNative_capacity
private theorem heapLengthRaw : 1 = (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2).1.length := by
  have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
  have bmp := (congrArg Prod.fst heapNative_same).trans (supported_native_bitmap heapWordWitness hs)
  exact (congrArg (fun bs => 1 = bs.length) bmp).mpr rfl


private theorem heapCapacityUnfold (optimized : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
  heapCapacityCondition optimized →
  let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
  optionLe (optionMap₂ max (some (max 1 (1+frame)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172) := by
  intro h
  exact h
private theorem heapCapacityRawExact : let raw := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))))
      let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig raw).2
      let entry := ((sptLookup 64 (sptFromAList optimized)).getD (1,.skip)).2
      let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
      let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
        (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList optimized)
      optionLe (optionMap₂ max (some (max 1 (1+frame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList optimized)))) (some 2097172) := by
  exact heapCapacityUnfold _ heapCapacityRaw


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The heap store/load program reaches the machine through the call-aware theorem
with a clock computed from its code and initial configuration. -/
private theorem heapFixture_machine :
    let native := (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2)
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (heapHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes native.2.2.2,native.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart native.2.2.2)) sourceFfi
      heapTicks (configuredMachineState native.2.2.2 native.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (heapHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  have shape : ScalarSupported heapWordWitness := heapWordWitness_supported
  have table : FunctionTableSupported heapFunctions := by
    intro f hf
    simp only [heapFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
    subst f
    refine ⟨?_,shape.1,?_,rfl⟩
    · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,shape.2]
    · simp
  have unique : ((functionsHOL (heapHOLFunctions.map DeclHOL.function)).map Prod.fst).Nodup := by
    simp [heapHOLFunctions,heapFunctions,funDeclToHOL,functionsHOL]
  let targetCode := HolFiniteMapExact.empty.updateList (functionsHOL (heapSimpFunctions.map DeclHOL.function)).reverse
  have span := countedCalls_initializedMachine shape heapProduction heapSource heapFunctions 1 7 table rfl rfl targetCode
    (functionsHOL (heapHOLFunctions.map DeclHOL.function)) (by rfl)
    heapHOLFunctions rfl unique heapSimpFunctions rfl (ofString "main") rfl rfl
    heapFound heap_noInline (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 7
    _ _ _ _ 7 heapSource_run (by rfl) heapBitmapFitRaw heapSafeRaw heapFactsRaw heapCapacityRawExact heapLengthRaw
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiled,sourceRun,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [heapProduction,functionSourceProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  refine ⟨compilerFinal,?_,machine,ffi,?_,outputEvents,?_⟩
  · exact compiled
  · dsimp only [heapTicks]
    exact machineRun
  · simpa [heapSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate] using semantics

end SteppedFlapjack.Concrete


/-! Concrete component weights of the heap store/load machine clock. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem heapStackWeight : stackCodeWeight (sptFromAList (supportedNative heapWordWitness).2.2.2) = 17 := by
  rw [heapNativeLiteral_eq]
  decide +kernel
private theorem heapWordWeight : wordCodeWeight (sptFromAList (supportedAllocated heapWordWitness).2) = 15 := by
  rw [heapOptimizedLiteral_eq]
  decide +kernel



private theorem heapEntries : functionsHOL (heapHOLFunctions.map DeclHOL.function) =
    [(ofString "main",[],progToHOL heapWordWitness,ShapeHOL.one)] := by
  simp only [heapHOLFunctions,heapFunctions,List.map,funDeclToHOL,functionsHOL,shapeToHOL]
private theorem heapSimpBody : panSimpCompileHOL (progToHOL heapWordWitness) = progToHOL heapWordWitness := by
  simp only [heapWordWitness,progToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL]
private theorem heapTableWeight : SimpVisits.simpTableFactor (functionsHOL (heapHOLFunctions.map DeclHOL.function)) = 4 := by
  rw [heapEntries]
  have generic (p : ProgHOL 64) : SimpVisits.simpTableFactor [(ofString "main",[],p,ShapeHOL.one)] =
      1 + max (SimpVisits.hw (panSimpCompileHOL p)) 0 := by rfl
  have hweight : SimpVisits.hw (progToHOL heapWordWitness) = 3 := by
    simp only [heapWordWitness,progToHOL,SimpVisits.hw]
  have h := generic (progToHOL heapWordWitness)
  have w := (congrArg SimpVisits.hw heapSimpBody).trans hweight
  have rhs : 1 + max (SimpVisits.hw (panSimpCompileHOL (progToHOL heapWordWitness))) 0 = 4 := by
    rw [w]
    decide
  exact h.trans rhs

private theorem heapBodyWeight : SimpVisits.hw (progToHOL (panSimpProg heapWordWitness)) = 3 := by
  simp [heapWordWitness,panSimpProg,seqAssoc,retToTail,smartSeq,seqCallRet,progToHOL,expToHOL,SimpVisits.hw]
private theorem heapCodeWeight : CrepSteps.codeWeight (crepPrograms (progToHOL (panSimpProg heapWordWitness))) = 7 := by
  rw [heapCrepTable]
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms]
private theorem heapClock_callFactor (ctx : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor ctx ((crepPrograms (progToHOL (panSimpProg heapWordWitness))).map (fun row => (row.2.1,row.2.2))) clock
      (.seq .skip (.call none (entryName (progToHOL (panSimpProg heapWordWitness))) [])) = 174 := by
  rw [heapCrepTable]
  simp [callClockFactor,callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]


/-- The source and generated-code weights in the concrete heap clock. -/
private theorem heapClock_staticWeights :
    SimpVisits.simpTableFactor (functionsHOL (heapHOLFunctions.map DeclHOL.function)) = 4 ∧
    SimpVisits.hw (progToHOL (panSimpProg heapWordWitness)) = 3 ∧
    CrepSteps.codeWeight (crepPrograms (progToHOL (panSimpProg heapWordWitness))) = 7 ∧
    loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL (panSimpProg heapWordWitness))))) = 42 ∧
    wordCodeWeight (sptFromAList (supportedAllocated heapWordWitness).2) = 15 ∧
    stackCodeWeight (sptFromAList (supportedNative heapWordWitness).2.2.2) = 17 :=
  ⟨heapTableWeight,heapBodyWeight,heapCodeWeight,heapLoopWeight,heapWordWeight,heapStackWeight⟩

/-- The concrete heap code gives the machine backend its fixed clock factor. -/
private theorem heapClock_targetFactor (cfg : Flapjack.Compiler.Backend.LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative heapWordWitness).2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [heapNativeLiteral_eq]
  unfold heapNativeLiteral
  decide +kernel
end SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem heapPrograms : compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")) = crepPrograms (progToHOL (panSimpProg heapWordWitness)) := by
  rw [heap_simpDeclarations]
  rfl
private theorem heapMain : newMainNameHOL (heapSimpFunctions.map DeclHOL.function) = entryName (progToHOL (panSimpProg heapWordWitness)) := by
  rw [heap_simpDeclarations]
  rfl
private theorem heapEntrySyntax (ctx : CrepToLoopContextExact) (name : MlString) :
    callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
  simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem heapEntryOpt (ctx : CrepToLoopContextExact) (name : MlString) :
    loopVisitWeight (optimiseHOL (compileHOLExact ctx .ln (.seq .skip (.call none name []) : CrepProgHOL 64))) = 10 := by
  have generic (lab : Nat) : loopVisitWeight (optimiseHOL
      (.seq .skip (.seq (.call none (some lab) [] none) .skip) : HolLoopProg 64)) = 10 := by
    simp [optimiseHOL,loopCallCompHOL,Flapjack.compHOL,shrinkHOL,markAllHOL,loopVisitWeight]
  simpa [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL] using generic (findLabExact ctx name)

private theorem heapRawLoopWeight : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))))) = 42 := by
  exact (congrArg (fun programs => loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) heapPrograms).mpr heapClock_staticWeights.2.2.2.1

private theorem heapFactors (ctx : CrepToLoopContextExact) (name : MlString)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (h : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) :
    max (callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64))
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44 := by
  rw [heapEntrySyntax,h]
  decide
private theorem heapOptFactors (ctx : CrepToLoopContextExact) (name : MlString)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (h : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) :
    max (loopVisitWeight (optimiseHOL (compileHOLExact ctx .ln (.seq .skip (.call none name []) : CrepProgHOL 64))))
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44 := by
  rw [heapEntryOpt,h]
  decide

private theorem heapBackendNumeric (code : List (Nat × HolProg 64)) (hfactor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64) (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) : callPipelineTicks code [4] 7 4 3 174 8 5 44 10 44 15 17 7 = 29426197640928697548 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold callPipelineTicks fixtureStackOracle
  dsimp only
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at hfactor
  rw [hfactor,uniform,init]
  simp [flattenStepFactor]

private theorem heapClock_fromInputs (code : List (Nat × HolProg 64)) (bitmap : List (BitVec 64))
  (cw tw pw cf i sw lf ow ofac ww stackw count : Nat)
  (a : code = (supportedNative heapWordWitness).2.2.2) (b : bitmap = [4])
  (c : cw = 7) (d : tw = 4) (e : pw = 3) (f : cf = 174) (g : i = 8)
  (h : sw = 5) (j : lf = 44) (k : ow = 10) (l : ofac = 44) (m : ww = 15) (n : stackw = 17) (o : count = 7) :
  callPipelineTicks code bitmap cw tw pw cf i sw lf ow ofac ww stackw count = 29426197640928697548 := by
  subst code; subst bitmap; subst cw; subst tw; subst pw; subst cf; subst i; subst sw; subst lf; subst ow; subst ofac; subst ww; subst stackw; subst count
  exact heapBackendNumeric _ (heapClock_targetFactor _)

/-- The heap witness clock, evaluated from its actual program and fixture. -/
private theorem heapClock_numeric : heapTicks = 29426197640928697548 := by
  unfold heapTicks
  apply heapClock_fromInputs
  case a => exact congrArg (fun n => n.2.2.2) heapNative_same
  case b =>
    have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
    exact (congrArg Prod.fst heapNative_same).trans (supported_native_bitmap heapWordWitness hs)
  case c =>
    simp only [heapPrograms,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    rw [heapClock_staticWeights.2.2.1]
    simp [CrepSteps.statementWeight]
  case j =>
    let programs := compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))
    change max (callSyntaxCost _ _) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44
    conv_lhs => arg 1; arg 2; simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapFactors (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0) (newMainNameHOL (heapSimpFunctions.map DeclHOL.function)) programs heapRawLoopWeight
  case l =>
    let programs := compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))
    change max (loopVisitWeight (optimiseHOL (compileHOLExact _ .ln _))) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44
    conv_lhs => arg 1; arg 1; arg 1; arg 3; simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapOptFactors (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0) (newMainNameHOL (heapSimpFunctions.map DeclHOL.function)) programs heapRawLoopWeight
  case d => exact heapClock_staticWeights.1
  case e => exact heapClock_staticWeights.2.1
  case g => rfl
  case h =>
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapEntrySyntax _ _
  case k =>
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapEntryOpt _ _
  case f =>
    simp only [heapPrograms,heapMain,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapClock_callFactor _ _
  case m =>
    have eq := congrArg (fun p => max 1 (wordCodeWeight (sptFromAList p.2))) heapAllocator_same
    exact eq.trans (by rw [heapClock_staticWeights.2.2.2.2.1]; decide)
  case n =>
    have eq := congrArg (fun p => max 1 (stackCodeWeight (sptFromAList p.2.2.2))) heapNative_same
    exact eq.trans (by rw [heapClock_staticWeights.2.2.2.2.2]; decide)
  case o => rfl

/-- The heap store/load program halts at its kernel-checked numeric clock. -/
theorem heapFixture_machine_numeric :
    let native := (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2)
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (heapHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes native.2.2.2,native.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart native.2.2.2)) sourceFfi
      29426197640928697548 (configuredMachineState native.2.2.2 native.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (heapHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  simpa only [heapClock_numeric] using heapFixture_machine

end SteppedFlapjack.Concrete
