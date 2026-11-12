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



theorem heap_simpDeclarations : heapSimpFunctions.map DeclHOL.function = declarations (progToHOL (panSimpProg heapWordWitness)) := by
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


theorem heapRaw_same : loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))) =
    supportedWordPrograms heapWordWitness := by
  unfold supportedWordPrograms crepPrograms
  rw [heap_simpDeclarations]



theorem heapAllocator_same : compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
    (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
      (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))))) =
    supportedAllocated heapWordWitness := by
  exact congrArg (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig) heapRaw_same


theorem heapNative_same :
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
theorem heapFixture_machine :
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
