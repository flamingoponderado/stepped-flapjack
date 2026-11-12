import SteppedFlapjack.Concrete.NestedFacts
import SteppedFlapjack.Concrete.SingletonMachine
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def nestedUnifiedSource := nestedCallDeclarations.map declToHOL
private def nestedUnifiedEntries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  [(ofString "main'",[],progToHOL nestedCallEntry,.one),
   (ofString "middle",[],progToHOL (.call none "leaf" [] : Prog (RiscV.Word 64)),.one),
   (ofString "leaf",[],progToHOL (.return (.const 7) : Prog (RiscV.Word 64)),.one)]
private def nestedUnifiedPost := singletonPost 2 6
private instance : DecidablePred nestedUnifiedPost.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
private instance : DecidablePred nestedUnifiedPost.shMemaddrs := by change DecidablePred sharedAddress; infer_instance
private def nestedUnifiedProduction := globalEntryProduction nestedUnifiedPost nestedUnifiedEntries
private theorem nestedUnifiedSupported : Supported (globalEntryShapes nestedUnifiedPost nestedUnifiedEntries) nestedCallEntry := by
  refine ⟨.call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp)))), ?_⟩
  simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]
private theorem nestedUnifiedEntriesSupported : GlobalSupportedEntries (globalEntryShapes nestedUnifiedPost nestedUnifiedEntries) nestedUnifiedEntries := by
  intro name params body ret found
  simp only [nestedUnifiedEntries,List.lookup] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact ⟨[],nestedCallEntry,rfl,rfl,nestedUnifiedSupported.1,nestedUnifiedSupported.2⟩
  · split at found
    · simp only [Option.some.injEq,Prod.mk.injEq] at found
      obtain ⟨rfl,rfl,rfl⟩ := found
      refine ⟨[],.call none "leaf" [],rfl,rfl,.tail "leaf" [] (by simp),?_⟩
      simp [ProgByteRanged,NameRanged]
    · split at found
      · simp only [Option.some.injEq,Prod.mk.injEq] at found
        obtain ⟨rfl,rfl,rfl⟩ := found
        refine ⟨[],.return (.const 7),rfl,rfl,.base (.ret (.const _)),?_⟩
        simp [ProgByteRanged,ExpByteRanged]
      · simp at found
private theorem nestedUnifiedRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) nestedUnifiedProduction.structs (countedFunctionsOfCode nestedUnifiedProduction.code)
    nestedUnifiedProduction.baseAddress nestedUnifiedProduction.topAddress panSemBitVec64BytesInWord 8
    nestedUnifiedProduction.locals nestedUnifiedProduction.globals nestedUnifiedProduction.memory nestedUnifiedProduction.ffi nestedCallEntry
    (memoryAccess := some (panSemBitVec64MemoryAccess nestedUnifiedProduction))
    (contracts := some (countedContractsOfCode nestedUnifiedProduction.code [])) =
      some (.returned (fun _ => none) nestedUnifiedProduction.globals nestedUnifiedProduction.memory nestedUnifiedProduction.ffi [.word 7],6) := by
  simp [nestedCallEntry,nestedUnifiedProduction,globalEntryProduction,panSemExecStateOfHOLWithKeys,globalEntrySource,
    installSourceFunctions,callEntryStateHOLFinite,panSemStateOfExactWithKeys,nestedUnifiedEntries,
    countedFunctionsOfCode,countedContractsOfCode,evalPanValueFfiProgSteps,evalPanValueFfiCallSteps,panValueCallArguments,
    evalPanValueExpsCounted,evalPanValueExps,evalPanValueExp.evalPanValueExps,panValueExpsStepCost,
    panValueExpStepCost.panValueExpsStepCost,panValueCallTarget,lookupPanFunction,lookupInfo,panValueParametersValid,
    panValueValuesMatchShapes,bindPanValueParameters,panValueReturnValid,panValueReturnResult,
    evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panShapeMatches,panValueShape,updatePanValueMap,
    restorePanValueFfiLocal,mlFunctionToInfoMap,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,
    panLangEntryOfHOL,progOfHOL,expOfHOL,shapeOfHOL,progToHOL,expToHOL,shapeToHOL,toStringOfBytes,ofString,MlString.explode_implode]
  funext name
  simp [restorePanValueLocal]

private theorem nestedUnifiedDeclarations : globalCompilerDecls nestedUnifiedSource = compileTopExactHOL nestedUnifiedSource (ofString "main") := by
  have fs : nestedUnifiedSource = (nestedSourceFunctions.map funDeclToHOL).map DeclHOL.function := by
    simp [nestedUnifiedSource,nestedSourceFunctions,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL]
  have fixed : (nestedSourceFunctions.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body}) = nestedSourceFunctions.map funDeclToHOL := by
    simp [nestedSourceFunctions,nestedCallEntry,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL]
  unfold globalCompilerDecls
  rw [fs,simpFunctions,call_structs_top nestedSourceFunctions nested_table_supported,fixed]
private theorem nestedUnifiedRows : functionsHOL (globalCompilerDecls nestedUnifiedSource) =
    (ofString "main",[],.seq (nestedSeqHOL []) (.call none (ofString "main'") []),.one) ::
      nestedUnifiedEntries.map (fun e => (e.1,e.2.1,compileProgExactHOL singletonGlobals e.2.2.1,e.2.2.2)) := by
  rw [nestedUnifiedDeclarations]
  simp [nestedUnifiedSource,nestedUnifiedEntries,singletonGlobals,beforeGlobalsContext,nestedSeqHOL,
    nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    compileTopExactHOL,functionsHOL,compileTopFunctionLookup_eq_lookup,List.lookup,resortDeclsHOL,newMainNameHOL,
    isNameHOL,isDeclHOL,isExnDeclHOL,freshNameMlS,mlstrAppend,ofString,MlString.explode_implode,
    compileProgExactHOL,compileExpExactHOL]
  dsimp only [List.filter,isFunctionHOL]
  simp [fpermDecsHOL,compileDecsExactHOL,decShapesHOL,fpermHOL,fpermName,compileProgExactHOL,compileExpExactHOL,
    functionsHOL]
private theorem nestedUnifiedNoInline : (functionsHOL ((globalCompilerDecls nestedUnifiedSource).filter inlinableHOL)).map Prod.fst = [] := by
  rw [nestedUnifiedDeclarations]
  exact nestedCall_inline_selection_empty
private theorem nestedUnifiedExceptions : (globalCompilerContext nestedUnifiedSource).eids = HolFiniteMapExact.empty := by
  unfold globalCompilerContext
  rw [nestedUnifiedDeclarations]
  exact nestedCall_noExceptions


private theorem nestedUnifiedSourceFs : nestedUnifiedSource = (nestedSourceFunctions.map funDeclToHOL).map DeclHOL.function := by
  simp [nestedUnifiedSource,nestedSourceFunctions,nestedCallDeclarations,nestedCallEntry,declToHOL,funDeclToHOL,progToHOL,expToHOL,shapeToHOL]
private theorem nestedUnifiedGood : pancakeGoodCodeHOL nestedUnifiedSource = true := by
  rw [nestedUnifiedSourceFs]
  exact table_good nestedSourceFunctions nested_table_supported
private theorem nestedUnifiedPrograms : globalSourcePrograms nestedUnifiedSource = nestedCallCrepPrograms := by
  change compileProgDeclsHOLW (globalCompilerDecls nestedUnifiedSource) = _
  rw [nestedUnifiedDeclarations]
  rfl
private theorem nestedUnifiedRaw : globalSourceRaw nestedUnifiedSource = nestedRawWords := by
  unfold globalSourceRaw nestedRawWords
  rw [nestedUnifiedPrograms]
private theorem nestedUnifiedWords : globalSourceWords nestedUnifiedSource = nestedOptimizedWords := by
  unfold globalSourceWords nestedOptimizedWords
  rw [nestedUnifiedRaw]
private theorem nestedUnifiedNative : globalSourceNative nestedUnifiedSource = nestedNative := by
  unfold globalSourceNative nestedNative
  rw [nestedUnifiedWords]
private theorem nestedUnifiedBitmaps : globalSourceBitmaps nestedUnifiedSource = [4,2] := by
  unfold globalSourceBitmaps
  rw [nestedUnifiedNative]
  exact nested_bitmaps
private theorem nestedUnifiedCode : globalSourceCode nestedUnifiedSource = nestedCode := by
  unfold globalSourceCode nestedCode
  rw [nestedUnifiedNative]
private theorem nestedUnifiedCapacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame nestedUnifiedSource)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames nestedUnifiedSource) 64
      (sptFromAList (globalSourceWords nestedUnifiedSource))))) (some 2097172) := by
  unfold globalSourceFrame globalSourceFrames globalSourceEntry
  rw [nestedUnifiedWords]
  exact nested_capacity
private theorem nestedUnifiedBefore : beforeGlobals (globalEntryTarget nestedUnifiedSource 6 singletonGlobals nestedUnifiedEntries) 0 0 = nestedUnifiedPost := by
  have noAddresses (a : BitVec 64) : ¬ addresses heapTop 0 a := by rw [mem_addresses]; simp
  have domain : (fun a => ordinaryAddress a ∧ ¬ addresses heapTop 0 a) = ordinaryAddress := by
    funext a
    exact propext (by simp [noAddresses])
  simp [nestedUnifiedPost,singletonPost,globalEntryTarget,installTargetFunctions,globalEntryTemplate,beforeGlobals,
    sourceTemplateFor,sourceTemplate,domain,nestedUnifiedBitmaps]
private theorem nestedUnifiedAllocated : ∀ a, addresses ((globalEntryTemplate nestedUnifiedSource 6).topAddr - panBytesInWord 64 *
      BitVec.ofNat 64 ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)
      ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum a → (globalEntryTemplate nestedUnifiedSource 6).memaddrs a := by
  intro a present
  rw [mem_addresses] at present
  obtain ⟨i,hi,_⟩ := present
  simp [decShapesHOL] at hi
private theorem nestedUnifiedMachine : ∃ (sourceFinal : PanSemStateFiniteExact 64 Unit), ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig nestedUnifiedSource =
      some (fixtureCodeBytes (globalSourceCode nestedUnifiedSource),globalSourceBitmaps nestedUnifiedSource,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode nestedUnifiedSource))) sourceFfi
      (initializedGlobalTicks nestedUnifiedSource 6 [] nestedUnifiedPost [] singletonGlobals nestedUnifiedEntries (ofString "main'") (globalCompilerContext nestedUnifiedSource))
      (configuredMachineState (globalSourceCode nestedUnifiedSource) (globalSourceBitmaps nestedUnifiedSource)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents ∧ FfiStateRel nestedUnifiedProduction.ffi sourceFinal.ffi := by
  have unique : ((functionsHOL nestedUnifiedSource).map Prod.fst).Nodup := by
    simp [nestedUnifiedSource,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]; decide
  apply initializedGlobal_counted_machine nestedUnifiedSource unique nestedUnifiedGood 6 [] nestedUnifiedPost [] [] [] singletonGlobals
    nestedUnifiedEntries (ofString "main'") nestedCallEntry nestedUnifiedSupported 7
    (by simp) (by simp) (by
      change some (beforeGlobals (globalEntryTarget nestedUnifiedSource 6 singletonGlobals nestedUnifiedEntries) 0 0) = _
      rw [nestedUnifiedBefore]) (by simp [compileDecsExactHOL,singletonGlobals,beforeGlobalsContext,decShapesHOL])
    nestedUnifiedAllocated (by decide) (by simp [nestedUnifiedEntries]) nestedUnifiedEntriesSupported
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 8 6
    (fun _ => none) nestedUnifiedProduction.globals nestedUnifiedProduction.memory nestedUnifiedProduction.ffi nestedUnifiedRun (by decide)
    nestedUnifiedRows nestedUnifiedNoInline nestedUnifiedExceptions
  · rw [nestedUnifiedBitmaps]; decide
  · rw [nestedUnifiedCode]; exact nested_nativeSafe
  · rw [nestedUnifiedCode]; exact nested_compilerFacts
  · exact nestedUnifiedCapacity


private theorem nestedUnifiedSourceRun :
    let production := functionSourceProduction nestedSourceFunctions 2 6
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
      production.structs (countedFunctionsOfCode production.code) production.baseAddress production.topAddress panSemBitVec64BytesInWord 8
      production.locals production.globals production.memory production.ffi nestedCallEntry
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) (contracts := some (countedContractsOfCode production.code [])) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word 7],6) := by
  have h := nestedCounted_run (fun a => some (.word (initialWordFor 2 a))) (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  simpa [functionSourceProduction,nestedSourceFunctions,nestedCountedProduction,nestedCallDeclarations,functionEntries,sourceProduction,
    panSemBitVec64MemoryAccess] using h
private instance : DecidablePred (functionSourceExact nestedSourceFunctions 2 6).memaddrs := by
  change DecidablePred ordinaryAddress
  infer_instance
private theorem nestedUnifiedSourceSemantics : PanSemStateFiniteExact.semanticsDecls {sourceTemplateFor 2 with clock := 0} (ofString "main") nestedUnifiedSource =
    .terminate .success sourceFfi.ioEvents := by
  let production := functionSourceProduction nestedSourceFunctions 2 6
  let source := functionSourceExact nestedSourceFunctions 2 6
  have related : PanSemStateRelExec production source.toExact := functionSource_related nestedSourceFunctions 2 6 (table_names _ nested_table_supported)
  have ranged : PanSemStateRelExecRanged production := by
    simp [production,functionSourceProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals production.locals := wordLocals_empty
  have codeRanged := table_code_ranged nestedSourceFunctions 2 6 nested_table_supported
  have codeShape := table_counted_shapes nestedSourceFunctions 2 6 nested_table_supported
  have shape : CallSupportedIn [] nestedCallEntry := .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  have programRanged : ProgByteRanged nestedCallEntry := by simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]
  obtain ⟨holResult,final,holRun,outcome,_,_⟩ := supportedCalls_counted_source shape
    production source related ranged words programRanged codeRanged codeShape
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 8 6 _ nestedUnifiedSourceRun (by rfl)
  cases outcome with
  | returned locals globals memory ffi word final nextRel nextRanged nextWords =>
    have wf := table_wellFormed nestedSourceFunctions nested_table_supported
    have unique : ((functionsHOL nestedUnifiedSource).map Prod.fst).Nodup := by
      simp [nestedUnifiedSource,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]; decide
    have found : (functionsHOL nestedUnifiedSource).lookup (ofString "main") = some ([],progToHOL nestedCallEntry,.one) := by
      simp [nestedUnifiedSource,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]
    have initialEq : ({(sourceTemplateFor 2) with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL nestedUnifiedSource).reverse), clock := 6} : PanSemStateFiniteExact 64 Unit) = source := by
      simp [source,functionSourceExact,nestedUnifiedSourceFs,sourceTemplateFor,sourceTemplate,List.map_map,Function.comp_def]
    have run' : (let declared := {(sourceTemplateFor 2) with clock := 0, structs := [], code :=
          (HolFiniteMapExact.empty.updateList (functionsHOL nestedUnifiedSource).reverse)}
        ({declared with clock := 6} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState (progToHOL nestedCallEntry)) =
          (some (.returned (.val (.word 7))),final) := by
      change ({(sourceTemplateFor 2) with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL nestedUnifiedSource).reverse), clock := 6} : PanSemStateFiniteExact 64 Unit).evaluateHOLFiniteState (progToHOL nestedCallEntry) = _
      rw [initialEq]
      exact holRun
    have behavior := functionOnly_body_semantics {(sourceTemplateFor 2) with clock := 0} (ofString "main")
      (nestedSourceFunctions.map funDeclToHOL) (progToHOL nestedCallEntry) wf (by simpa [nestedUnifiedSourceFs] using unique) rfl rfl
      (by simpa [nestedUnifiedSourceFs] using found) 6 final 7 run'
    have h := nextRel.2.2.2.2.2.2.2.2.2.2.1.2.1
    have events : final.ffi.ioEvents = [] := by
      change FfiEventListRel [] final.ffi.ioEvents at h
      cases heq : final.ffi.ioEvents with
      | nil => rfl
      | cons e es => simp [heq,FfiEventListRel] at h
    simpa [nestedUnifiedSourceFs,sourceFfi,events] using behavior


open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps
private theorem nestedUnifiedOptOfWeights (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (limit : Nat) (c : CrepToLoopContextExact) (entry : MlS)
    (body : compileProgExactHOLW panCtxt p = .seq .skip (.call none entry []))
    (sourceLimit : limit = 9) (crepClock : crep.clock = 7)
    (cw : CrepSteps.codeWeight programs = 4)
    (lw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 26)
    (cf : callClockFactor c (programs.map (fun row => (row.2.1,row.2.2))) 7 (.seq .skip (.call none entry [])) = 126)
    (sw : callSyntaxCost c (.seq .skip (.call none entry []) : CrepProgHOL 64) = 5)
    (ow : loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none entry []) : CrepProgHOL 64))) = 10) :
    loweredProgramOptLimit panCtxt p crep programs limit c c .ln = 7321282 := by
  unfold loweredProgramOptLimit
  dsimp only
  rw [body,sourceLimit,crepClock,cw,lw,cf,sw,ow]
  simp [CrepSteps.statementWeight]
private theorem nestedUnifiedOpt :
    let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nestedUnifiedSource)) 0
    loweredProgramOptLimit (globalCompilerContext nestedUnifiedSource) (.seq (nestedSeqHOL []) (.call none (ofString "main'") []))
      (globalEntryCrep nestedUnifiedSource 6 singletonGlobals nestedUnifiedEntries) (globalSourcePrograms nestedUnifiedSource)
      (2*(([] : List (DeclHOL 64)).length)+(callEntryStateHOLFinite (installSourceFunctions nestedUnifiedPost nestedUnifiedEntries) HolFiniteMapExact.empty).clock+3)
      context context .ln = 7321282 := by
  dsimp only
  apply nestedUnifiedOptOfWeights _ _ _ _ _ _ (ofString "main'")
  · simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
  · rfl
  · rfl
  · rw [nestedUnifiedPrograms,nestedCallCrepPrograms,nestedCall_crep_code]; rfl
  · rw [nestedUnifiedPrograms,nestedCall_loop_code]
    with_unfolding_all decide
  · rw [nestedUnifiedPrograms,nestedCallCrepPrograms,nestedCall_crep_code]
    with_unfolding_all rfl
  · simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
  · have generic (lab : Nat) : loopVisitWeight (optimiseHOL
        (.seq .skip (.seq (.call none (some lab) [] none) .skip) : HolLoopProg 64)) = 10 := by
      simp [optimiseHOL,loopCallCompHOL,Flapjack.compHOL,shrinkHOL,markAllHOL,loopVisitWeight]
    simpa [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL] using generic (findLabExact _ (ofString "main'"))


open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem nestedUnifiedNumericBackend (code : List (Nat × HolProg 64))
    (factorTwo : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4,2] (fixtureStackOracle (fixtureCompilerConfig code)) = 2919)
    (factorOne : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4,2] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 57 * (6*7321282+1 + ((13+1)*(6*7321282+1)+1))) = 5924092061654822880 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factorTwo factorOne
  rw [factorTwo,factorOne,uniform,init]
  norm_num [flattenStepFactor]
private theorem nestedUnifiedNumericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4,2]) (optEq : opt = 7321282) (wordEq : ww = 13) (stackEq : sw = 57)
    (factorTwo : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4,2] (fixtureStackOracle (fixtureCompilerConfig code)) = 2919)
    (factorOne : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 5924092061654822880 := by
  subst bs; subst opt; subst ww; subst sw
  exact nestedUnifiedNumericBackend code factorTwo factorOne

private theorem nestedUnifiedClockFromInputs
    (wordEq : wordCodeWeight (sptFromAList (globalSourceWords nestedUnifiedSource)) = 13)
    (stackEq : stackCodeWeight (sptFromAList (globalSourceCode nestedUnifiedSource)) = 57)
    (factorTwo : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode nestedUnifiedSource))) [4,2]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode nestedUnifiedSource))) = 2919)
    (factorOne : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode nestedUnifiedSource))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode nestedUnifiedSource))) = 1950) :
    initializedGlobalTicks nestedUnifiedSource 6 [] nestedUnifiedPost [] singletonGlobals nestedUnifiedEntries (ofString "main'")
      (globalCompilerContext nestedUnifiedSource) = 5924092061654822880 := by
  unfold initializedGlobalTicks
  dsimp only
  exact nestedUnifiedNumericFromInputs _ _ _ _ _ nestedUnifiedBitmaps nestedUnifiedOpt wordEq stackEq factorTwo factorOne

private theorem nestedWordTransfer (a b : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (h : a = b)
    (w : wordCodeWeight (sptFromAList b) = 13) : wordCodeWeight (sptFromAList a) = 13 := by rw [h]; exact w
private theorem nestedStackTransfer (a b : List (Nat × HolProg 64)) (h : a = b)
    (w : stackCodeWeight (sptFromAList b) = 57) : stackCodeWeight (sptFromAList a) = 57 := by rw [h]; exact w
private theorem nestedFactorTransfer (a b : List (Nat × HolProg 64)) (h : a = b) (bs : List (BitVec 64)) (value : Nat)
    (f : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf b)) bs (fixtureStackOracle (fixtureCompilerConfig b)) = value) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf a)) bs (fixtureStackOracle (fixtureCompilerConfig a)) = value := by rw [h]; exact f


private theorem nestedUnifiedClock : initializedGlobalTicks nestedUnifiedSource 6 [] nestedUnifiedPost [] singletonGlobals nestedUnifiedEntries (ofString "main'")
    (globalCompilerContext nestedUnifiedSource) = 5924092061654822880 := by
  apply nestedUnifiedClockFromInputs
  · exact nestedWordTransfer _ _ nestedUnifiedWords nested_wordWeightValue
  · exact nestedStackTransfer _ _ nestedUnifiedCode nested_stackWeightValue
  · exact nestedFactorTransfer _ _ nestedUnifiedCode [4,2] 2919 (nested_costFactorTwo _)
  · exact nestedFactorTransfer _ _ nestedUnifiedCode [4] 1950 (nested_costFactorOne _)
/-- The original nested-call source reaches its initialized machine at a concrete clock. -/
theorem nested_initialized_machine :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (nestedCallDeclarations.map declToHOL) = some (fixtureCodeBytes nestedCode,[4,2],compilerFinal) ∧
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart nestedCode)) sourceFfi
        5924092061654822880 (configuredMachineState nestedCode [4,2]) = (.halt .success,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = sourceFfi.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplateFor 2 with clock := 0} (ofString "main")
        (nestedCallDeclarations.map declToHOL) = .terminate .success finalFfi.ioEvents := by
  obtain ⟨sourceFinal,machine,ffi,compiler,compiled,run,events,ffiRel⟩ := nestedUnifiedMachine
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] sourceFinal.ffi.ioEvents at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have machineEvents : ffi.ioEvents = sourceFfi.ioEvents := by simpa [sourceFfi,sourceEvents] using events
  rw [nestedUnifiedCode,nestedUnifiedBitmaps] at compiled run
  rw [nestedUnifiedClock] at run
  refine ⟨compiler,compiled,machine,ffi,run,machineEvents,?_⟩
  rw [machineEvents]
  exact nestedUnifiedSourceSemantics

end SteppedFlapjack.Concrete
