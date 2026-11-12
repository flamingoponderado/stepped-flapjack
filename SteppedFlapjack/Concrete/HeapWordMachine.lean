import SteppedFlapjack.Concrete.HeapWordNativeFacts
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
import SteppedFlapjack.Concrete.GlobalCountedMachine
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def heapFunctions : List (FunDeclOf 64) := [⟨"main",false,false,[],heapWordWitness,.one⟩]
def heapHOLFunctions := heapFunctions.map funDeclToHOL
def heapSimpFunctions := heapHOLFunctions.map (fun f => {f with body := panSimpCompileHOL f.body})
def heapSourceProgram := heapHOLFunctions.map DeclHOL.function
private def name : MlS := entryName (progToHOL heapWordWitness)
private def entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) := [(name,[],progToHOL heapWordWitness,.one)]
private def globals : PanGlobalsContextExact 64 := beforeGlobalsContext 0
private def target := globalEntryTarget heapSourceProgram 7 globals entries
private theorem tableSupported : FunctionTableSupported heapFunctions := by
  intro f hf
  simp only [heapFunctions,List.mem_cons,List.not_mem_nil,or_false] at hf
  subst f
  refine ⟨?_,heapWordWitness_supported.1,?_,rfl⟩
  · simp [FunDeclByteRanged,ListParamByteRanged,ShapeByteRanged,NameRanged,heapWordWitness_supported.2]
  · simp
private theorem simpFixed : panSimpProg heapWordWitness = heapWordWitness := by
  simp [heapWordWitness,panSimpProg,seqAssoc,retToTail,smartSeq,seqCallRet]
private theorem simpDeclarations : heapSimpFunctions.map DeclHOL.function = declarations (progToHOL heapWordWitness) := by
  simp [heapSimpFunctions,heapHOLFunctions,heapFunctions,declarations,singleEntryProgram,funDeclToHOL,progToHOL,expToHOL,shapeToHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL,heapWordWitness]
private theorem programsEq : globalSourcePrograms heapSourceProgram = crepPrograms (progToHOL heapWordWitness) := by
  unfold globalSourcePrograms heapSourceProgram
  rw [simpFunctions]
  change compileProgDeclsHOLW (compileTopExactHOL
    (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (heapSimpFunctions.map DeclHOL.function)) (ofString "main")) = _
  have fixed : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (heapSimpFunctions.map DeclHOL.function) = heapSimpFunctions.map DeclHOL.function := by
    exact call_structs_top heapFunctions tableSupported
  rw [fixed,simpDeclarations]
  rfl
private theorem rawEq : globalSourceRaw heapSourceProgram = supportedWordPrograms heapWordWitness := by
  unfold globalSourceRaw supportedWordPrograms
  rw [programsEq,simpFixed]
private theorem nativeEqOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program) : globalSourceNative source = supportedNative program := by
  unfold globalSourceNative globalSourceWords supportedNative supportedAllocated
  rw [h]
private theorem bitmapOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program) (bm : (supportedNative program).1 = [4]) :
    globalSourceBitmaps source = [4] := by
  unfold globalSourceBitmaps
  rw [nativeEqOfRaw source program h]
  exact bm
private theorem bitmaps : globalSourceBitmaps heapSourceProgram = [4] := by
  have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))),heapWordWitness_ranged⟩
  exact bitmapOfRaw heapSourceProgram heapWordWitness rawEq (supported_native_bitmap heapWordWitness hs)
private def post := {sourceTemplate with clock := 8}
private theorem addressEmpty (a : BitVec 64) : ¬ addresses heapTop 0 a := by
  rw [mem_addresses]
  simp
private theorem beforeEq : beforeGlobals target 0 0 = post := by
  have domain : (fun a => ordinaryAddress a ∧ ¬ addresses heapTop 0 a) = ordinaryAddress := by
    funext a
    exact propext (by simp [addressEmpty])
  unfold target globalEntryTarget globalEntryTemplate
  rw [bitmaps]
  simp [post,installTargetFunctions,beforeGlobals,sourceTemplateFor,sourceTemplate,domain,initialWordFor_one]
private instance : DecidablePred post.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
private instance : DecidablePred post.shMemaddrs := by change DecidablePred sharedAddress; infer_instance
private theorem declEval : @evaluateDeclsHOLFinite 64 Unit _
    (beforeGlobals target (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)
      ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)
    (fun _ => Classical.propDecidable _) [] = some post := by
  change some (beforeGlobals target 0 0) = some post
  rw [beforeEq]
private theorem compiled : compileDecsExactHOL
    (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)) [] =
    ([],[],[],globals) := by simp [compileDecsExactHOL,globals,beforeGlobalsContext,decShapesHOL]
private theorem supported : Supported (globalEntryShapes post entries) heapWordWitness := heapWordWitness_supported.toSupported _
private theorem table : GlobalSupportedEntries (globalEntryShapes post entries) entries := by
  intro n ps body ret found
  simp only [entries,List.lookup] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact ⟨[],heapWordWitness,rfl,rfl,supported.1,supported.2⟩
  · simp at found
private theorem canonicalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) (globalEntryProduction post entries).structs
    (countedFunctionsOfCode (globalEntryProduction post entries).code)
    (globalEntryProduction post entries).baseAddress (globalEntryProduction post entries).topAddress
    panSemBitVec64BytesInWord 10 (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
    (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi heapWordWitness
    (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction post entries)))
    (contracts := some (countedContractsOfCode (globalEntryProduction post entries).code [])) =
      some (.returned (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
        (updatePanValueMemory (globalEntryProduction post entries).memory 0xa1000100 (.word 7))
        (globalEntryProduction post entries).ffi [.word 7],7) := by
  with_unfolding_all rfl
private def ctxt := frontendContext (progToHOL heapWordWitness)
private theorem callFree : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))),heapWordWitness_ranged⟩
private theorem tableEq : globalSourcePrograms heapSourceProgram = twoPrograms (ofString "main") name (supportedCallee (progToHOL heapWordWitness)) := by
  rw [programsEq,supported_crepPrograms heapWordWitness callFree]
  rfl
private theorem firstRow : globalSourcePrograms heapSourceProgram =
    (ofString "main",[],compileProgExactHOLW ctxt (.seq (nestedSeqHOL []) (.call none name []))) ::
      [(name,[],supportedCallee (progToHOL heapWordWitness))] := by
  rw [tableEq]
  simp [twoPrograms,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
private theorem sources : ∀ row ∈ globalSourcePrograms heapSourceProgram, ∃ (c : PanToCrepContextExact 64) (p : ProgHOL 64),
    row.2.2 = compileProgExactHOLW c p ∧ CallFrontend c p := by
  intro row member
  rw [tableEq] at member
  simp only [twoPrograms,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · refine ⟨ctxt,.seq .skip (.call none name []),?_,.seq (.base .skip) (.tail (by simp))⟩
    simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  · exact ⟨_,progToHOL heapWordWitness,rfl,.base (supported_frontend_shape callFree _)⟩
private theorem targetEq : (globalEntryTarget heapSourceProgram 7 globals entries).code =
    HolFiniteMapExact.empty.update (name,([],progToHOL heapWordWitness,.one)) := by
  simp [globalEntryTarget,installTargetFunctions,entries,HolFiniteMapExact.updateList,HolFiniteMapExact.update,FUPDATE_LIST,
    supported_globals_fixed callFree globals]
private theorem crepEq : (globalEntryCrep heapSourceProgram 7 globals entries).code = (crepState (progToHOL heapWordWitness)).code := by
  simp [globalEntryCrep,crepState,concreteDeclCrepState,programsEq]
private theorem fullLookup : (loweredState (progToHOL heapWordWitness)).code.lookup name = some ([],progToHOL heapWordWitness,.one) := by
  have rename := supported_fperm callFree (ofString "main") name
  have global := supported_globals_fixed callFree emptyGlobalsContext
  have fresh : name ≠ ofString "main" := entryName_fresh (progToHOL heapWordWitness)
  simp only [name] at rename fresh
  simp [loweredState,noGlobalsLoweredPreCall,loweredCode,lowered_declarations,functionsHOL,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,rename,global,Ne.symm fresh,name]
private theorem panCode : codeRelExactHOLW ctxt (globalEntryTarget heapSourceProgram 7 globals entries).code (globalEntryCrep heapSourceProgram 7 globals entries).code := by
  intro n ps body ret found
  rw [targetEq] at found
  simp only [HolFiniteMapExact.lookup_update,FUPDATE] at found
  split at found
  · rename_i equal
    have keyEq : name = n := beq_iff_eq.mp equal
    subst n
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    rw [crepEq]
    exact supported_code_related heapWordWitness callFree name [] (progToHOL heapWordWitness) .one fullLookup
  · simp [HolFiniteMapExact.lookup_empty] at found
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
private theorem safetyOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program)
    (safe : fixtureStackSafe (supportedNative program).2.2.2 = true) : fixtureStackSafe (globalSourceCode source) = true := by
  unfold globalSourceCode
  rw [nativeEqOfRaw source program h]
  exact safe
private theorem factsOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program)
    (facts : (fixtureRemoveLabels (supportedNative program).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative program).2.2.2).length % 4 = 0) :
    (fixtureRemoveLabels (globalSourceCode source)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode source)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode source)).length % 4 = 0 := by
  unfold globalSourceCode
  rw [nativeEqOfRaw source program h]
  exact facts
private theorem safety : fixtureStackSafe (globalSourceCode heapSourceProgram) = true := safetyOfRaw heapSourceProgram heapWordWitness rawEq heapNative_safe
private theorem facts : (fixtureRemoveLabels (globalSourceCode heapSourceProgram)).isSome = true ∧
    (fixtureCodeBytes (globalSourceCode heapSourceProgram)).length ≤ 0xecc ∧ (fixtureCodeBytes (globalSourceCode heapSourceProgram)).length % 4 = 0 :=
  factsOfRaw heapSourceProgram heapWordWitness rawEq heapNative_compilerFacts
private theorem allocated : ∀ a, addresses ((globalEntryTemplate heapSourceProgram 7).topAddr - panBytesInWord 64 *
    BitVec.ofNat 64 ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum)
    ((decShapesHOL ([] : List (DeclHOL 64))).map sizeOfShapeHOL).sum a → (globalEntryTemplate heapSourceProgram 7).memaddrs a := by
  intro a present
  change addresses heapTop 0 a at present
  exact False.elim (addressEmpty a present)
private theorem sourceUnique : ((functionsHOL heapSourceProgram).map Prod.fst).Nodup := by
  simp [heapSourceProgram,heapHOLFunctions,heapFunctions,funDeclToHOL,functionsHOL]
private theorem sourceGood : pancakeGoodCodeHOL heapSourceProgram = true := by with_unfolding_all decide
private theorem varsEmpty : ctxt.vars = HolFiniteMapExact.empty := by rfl
private theorem exceptionsEmpty : ctxt.eids = HolFiniteMapExact.empty := by
  simp [ctxt,frontendContext,declarations,singleEntry_compiled_eids_empty,mkCtxtExactHOL]
private def capacityOfWords (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) : Prop :=
  let entry := ((sptLookup 64 (sptFromAList words)).getD (1,.skip)).2
  let frame := (compileProgNative riscvConfig false entry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
  let frames := sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList words)
  optionLe (optionMap₂ max (some (max 1 (1+frame)))
    (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList words)))) (some 2097172)
private theorem wordsEqOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program) : globalSourceWords source = (supportedAllocated program).2 := by
  unfold globalSourceWords supportedAllocated
  rw [h]
private theorem capacityFromRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program) (cap : capacityOfWords (supportedAllocated program).2) :
    optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame source)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames source) 64 (sptFromAList (globalSourceWords source))))) (some 2097172) := by
  change capacityOfWords (globalSourceWords source)
  rw [wordsEqOfRaw source program h]
  exact cap
private theorem capacityProgram : capacityOfWords (supportedAllocated heapWordWitness).2 := by
  rw [heapOptimizedLiteral_eq]
  exact heapNative_capacity
private theorem capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame heapSourceProgram)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames heapSourceProgram) 64 (sptFromAList (globalSourceWords heapSourceProgram))))) (some 2097172) :=
  capacityFromRaw heapSourceProgram heapWordWitness rawEq capacityProgram
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
noncomputable def heapUnifiedTicks : Nat :=
  initializedGlobalTicks heapSourceProgram 7 [] post [] globals entries name ctxt
private theorem machine : ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig heapSourceProgram =
      some (fixtureCodeBytes (globalSourceCode heapSourceProgram),globalSourceBitmaps heapSourceProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode heapSourceProgram))) sourceFfi
      heapUnifiedTicks (configuredMachineState (globalSourceCode heapSourceProgram) (globalSourceBitmaps heapSourceProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  have bits : 0xa0020018 + (globalSourceBitmaps heapSourceProgram).length*8 ≤ 0xa0410000 := by rw [bitmaps]; decide
  have all := initializedGlobal_counted_machine heapSourceProgram sourceUnique sourceGood 7 [] post [] [] [] globals
    entries name heapWordWitness supported ctxt 7
    (by simp) (by simp) declEval compiled allocated (by decide)
    (by simp [entries]) table
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 7
    (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
    (updatePanValueMemory (globalEntryProduction post entries).memory 0xa1000100 (.word 7))
    (globalEntryProduction post entries).ffi canonicalRun (by decide)
    panCode varsEmpty exceptionsEmpty sources [(name,[],supportedCallee (progToHOL heapWordWitness))] firstRow
    bits safety facts capacity
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiledOutput,machineRun,events,ffiRel⟩ := all
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] sourceFinal.ffi.ioEvents at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  refine ⟨machine,ffi,compilerFinal,compiledOutput,?_,?_⟩
  · exact machineRun
  · simpa [sourceFfi,sourceEvents] using events

private theorem wrapper : compileProgExactHOLW ctxt (.seq (nestedSeqHOL []) (.call none name [])) =
    .seq .skip (.call none name []) := by
  simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,nestedSeqHOL]
private theorem codeWeight : CrepSteps.codeWeight (globalSourcePrograms heapSourceProgram) = 7 := by
  have tab := heapCrepTable
  rw [simpFixed] at tab
  rw [programsEq,tab]
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,twoPrograms]
private theorem loopWeight : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms heapSourceProgram))) = 42 := by
  rw [programsEq]
  have h := heapLoopWeight
  rw [simpFixed] at h
  exact h
private theorem callFactor (c : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor c ((globalSourcePrograms heapSourceProgram).map (fun row => (row.2.1,row.2.2))) clock
      (.seq .skip (.call none name [])) = 174 := by
  have tab := heapCrepTable
  rw [simpFixed] at tab
  rw [programsEq,tab]
  simp [callClockFactor,callTableCost,twoPrograms,callSyntaxCost,callExpressionCost,callArgumentsCost,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem syntaxWeight (c : CrepToLoopContextExact) :
    callSyntaxCost c (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
  simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem optWeight (c : CrepToLoopContextExact) :
    loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none name []) : CrepProgHOL 64))) = 10 := by
  have generic (lab : Nat) : loopVisitWeight (optimiseHOL
      (.seq .skip (.seq (.call none (some lab) [] none) .skip) : HolLoopProg 64)) = 10 := by
    simp [optimiseHOL,loopCallCompHOL,Flapjack.compHOL,shrinkHOL,markAllHOL,loopVisitWeight]
  simpa [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL] using generic (findLabExact c name)
private theorem optOfWeights (panCtxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (crep : CrepSemHOLState 64 Unit) (programs : List (MlS × List Nat × CrepProgHOL 64))
    (limit : Nat) (c : CrepToLoopContextExact) (entry : MlS)
    (body : compileProgExactHOLW panCtxt p = .seq .skip (.call none entry []))
    (sourceLimit : limit = 10) (crepClock : crep.clock = 8)
    (cw : CrepSteps.codeWeight programs = 7)
    (lw : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42)
    (cf : callClockFactor c (programs.map (fun row => (row.2.1,row.2.2))) 8 (.seq .skip (.call none entry [])) = 174)
    (sw : callSyntaxCost c (.seq .skip (.call none entry []) : CrepProgHOL 64) = 5)
    (ow : loopVisitWeight (optimiseHOL (compileHOLExact c .ln (.seq .skip (.call none entry []) : CrepProgHOL 64))) = 10) :
    loweredProgramOptLimit panCtxt p crep programs limit c c .ln = 47866114 := by
  unfold loweredProgramOptLimit
  dsimp only
  rw [body,sourceLimit,crepClock,cw,lw,cf,sw,ow]
  simp [CrepSteps.statementWeight]
private theorem optLimit :
    let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms heapSourceProgram)) 0
    loweredProgramOptLimit ctxt (.seq (nestedSeqHOL []) (.call none name [])) (globalEntryCrep heapSourceProgram 7 globals entries)
      (globalSourcePrograms heapSourceProgram) (2*(([] : List (DeclHOL 64)).length)+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3)
      context context .ln = 47866114 := by
  dsimp only
  apply optOfWeights _ _ _ _ _ _ name wrapper (by rfl) (by rfl) codeWeight loopWeight
  · exact callFactor _ 8
  · exact syntaxWeight _
  · exact optWeight _
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem wordWeight : wordCodeWeight (sptFromAList (supportedAllocated heapWordWitness).2) = 15 := by
  rw [heapOptimizedLiteral_eq]
  decide +kernel
private theorem stackWeight : stackCodeWeight (sptFromAList (supportedNative heapWordWitness).2.2.2) = 17 := by
  rw [heapNativeLiteral_eq]
  decide +kernel
private theorem wordWeightOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program)
    (w : wordCodeWeight (sptFromAList (supportedAllocated program).2) = 15) :
    wordCodeWeight (sptFromAList (globalSourceWords source)) = 15 := by
  rw [wordsEqOfRaw source program h]
  exact w
private theorem stackWeightOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program)
    (w : stackCodeWeight (sptFromAList (supportedNative program).2.2.2) = 17) :
    stackCodeWeight (sptFromAList (globalSourceCode source)) = 17 := by
  unfold globalSourceCode
  rw [nativeEqOfRaw source program h]
  exact w
private theorem targetFactor (cfg : Flapjack.Compiler.Backend.LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative heapWordWitness).2.2.2)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  rw [heapNativeLiteral_eq]
  unfold heapNativeLiteral
  decide +kernel
private theorem factorOfRaw (source : List (DeclHOL 64)) (program : Prog (RiscV.Word 64))
    (h : globalSourceRaw source = supportedWordPrograms program)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (supportedNative program).2.2.2)) [4]
      (fixtureStackOracle (fixtureCompilerConfig (supportedNative program).2.2.2)) = 1950) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode source))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode source))) = 1950 := by
  unfold globalSourceCode
  rw [nativeEqOfRaw source program h]
  exact factor
private theorem numericBackend (code : List (Nat × HolProg 64))
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 17 * (6*47866114+1 + ((15+1)*(6*47866114+1)+1))) = 8745709949718150348 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
private theorem numericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 47866114) (wordEq : ww = 15) (stackEq : sw = 17)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 8745709949718150348 := by
  subst bs; subst opt; subst ww; subst sw
  exact numericBackend code factor
private theorem numericTicks (source : List (DeclHOL 64)) (clock : Nat) (decs : List (DeclHOL 64))
    (after : PanSemStateFiniteExact 64 Unit) (inits : List (ProgHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (functions : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (entry : MlS)
    (panContext : PanToCrepContextExact 64)
    (bitmap : globalSourceBitmaps source = [4])
    (optEq : let context := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms source)) 0
      loweredProgramOptLimit panContext (.seq (nestedSeqHOL inits) (.call none entry [])) (globalEntryCrep source clock globalContext functions)
        (globalSourcePrograms source) (2*decs.length+(callEntryStateHOLFinite (installSourceFunctions after functions) HolFiniteMapExact.empty).clock+3)
        context context .ln = 47866114)
    (wordEq : wordCodeWeight (sptFromAList (globalSourceWords source)) = 15)
    (stackEq : stackCodeWeight (sptFromAList (globalSourceCode source)) = 17)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf (globalSourceCode source))) [4]
      (fixtureStackOracle (fixtureCompilerConfig (globalSourceCode source))) = 1950) :
    initializedGlobalTicks source clock decs after inits globalContext functions entry panContext = 8745709949718150348 := by
  unfold initializedGlobalTicks
  dsimp only
  exact numericFromInputs _ _ _ _ _ bitmap optEq wordEq stackEq factor
private theorem clockNumeric : heapUnifiedTicks = 8745709949718150348 := by
  exact numericTicks heapSourceProgram 7 [] post [] globals entries name ctxt bitmaps optLimit
    (wordWeightOfRaw heapSourceProgram heapWordWitness rawEq wordWeight)
    (stackWeightOfRaw heapSourceProgram heapWordWitness rawEq stackWeight)
    (factorOfRaw heapSourceProgram heapWordWitness rawEq (targetFactor _))
private def originalProduction := functionSourceProduction heapFunctions 1 7
private def originalSource := functionSourceExact heapFunctions 1 7
private instance : DecidablePred originalSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
private theorem originalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) originalProduction.structs (countedFunctionsOfCode originalProduction.code)
    originalProduction.baseAddress originalProduction.topAddress panSemBitVec64BytesInWord 10
    originalProduction.locals originalProduction.globals originalProduction.memory originalProduction.ffi heapWordWitness
    (memoryAccess := some (panSemBitVec64MemoryAccess originalProduction))
    (contracts := some (countedContractsOfCode originalProduction.code [])) =
      some (.returned originalProduction.locals originalProduction.globals
        (updatePanValueMemory originalProduction.memory 0xa1000100 (.word 7)) originalProduction.ffi [.word 7],7) := by
  have hs : SupportedIn [] heapWordWitness := .seq (.store (.const _) (.const _)) (.ret (.load (.const _)))
  rw [supported_calls_irrel _ _ _ originalProduction.structs (countedFunctionsOfCode originalProduction.code) []
    originalProduction.baseAddress originalProduction.topAddress panSemBitVec64BytesInWord 10
    (some (panSemBitVec64MemoryAccess originalProduction)) (some (countedContractsOfCode originalProduction.code [])) [] heapWordWitness hs]
  simpa [panSemBitVec64BytesInWord,originalProduction,functionSourceProduction,sourceProduction,initialWordFor_one,
    executableState,singleEntrySourceProduction,panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,
    panSemBitVec64WordModel,panSemWordModel,RiscV.panRiscVMemoryModel] using heapWordWitness_run
private theorem sourceSemantics : semanticsDecls {sourceTemplate with clock := 0} (ofString "main") heapSourceProgram =
    .terminate .success sourceFfi.ioEvents := by
  have related : PanSemStateRelExec originalProduction originalSource.toExact :=
    functionSource_related heapFunctions 1 7 (table_names heapFunctions tableSupported)
  have ranged : PanSemStateRelExecRanged originalProduction := by
    simp [originalProduction,functionSourceProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals originalProduction.locals := wordLocals_empty
  have codeRanged := table_code_ranged heapFunctions 1 7 tableSupported
  have codeShape := table_counted_shapes heapFunctions 1 7 tableSupported
  obtain ⟨holResult,final,holRun,outcome,_,_⟩ := supportedCalls_counted_source heapWordWitness_supported.1
    originalProduction originalSource related ranged words heapWordWitness_ranged codeRanged codeShape
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 7 _ originalRun (by decide)
  cases outcome with
  | returned locals globals memory ffi word final nextRel nextRanged nextWords =>
    have wf : heapHOLFunctions.all (fun f => f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
        isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true := by
      simp [heapHOLFunctions,heapFunctions,funDeclToHOL,shapeToHOL,isWfShapeExactHOL]
    have found : (functionsHOL (heapHOLFunctions.map DeclHOL.function)).lookup (ofString "main") =
        some ([],progToHOL heapWordWitness,.one) := by
      simp [heapHOLFunctions,heapFunctions,funDeclToHOL,functionsHOL,shapeToHOL]
    have initialEq : ({sourceTemplate with structs := [], code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (heapHOLFunctions.map DeclHOL.function)).reverse), clock := 7} : PanSemStateFiniteExact 64 Unit) = originalSource := by
      simp [originalSource,functionSourceExact,sourceTemplateFor_one,sourceTemplate,heapHOLFunctions,List.map_map,Function.comp_def]
    have behavior := functionOnly_body_semantics {sourceTemplate with clock := 0} (ofString "main") heapHOLFunctions
      (progToHOL heapWordWitness) wf sourceUnique rfl rfl found 7 final 7 (by simpa [initialEq] using holRun)
    have finalEvents : final.ffi.ioEvents = [] := by
      have h := nextRel.2.2.2.2.2.2.2.2.2.2.1.2.1
      change FfiEventListRel [] final.ffi.ioEvents at h
      cases heq : final.ffi.ioEvents with
      | nil => rfl
      | cons e es => simp [heq,FfiEventListRel] at h
    simpa [heapSourceProgram,sourceFfi,finalEvents] using behavior
/-- The heap store/load source and its compiled machine agree at a concrete clock. -/
theorem heapFixture_machine_numeric : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig heapSourceProgram =
      some (fixtureCodeBytes (globalSourceCode heapSourceProgram),globalSourceBitmaps heapSourceProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode heapSourceProgram))) sourceFfi
      8745709949718150348 (configuredMachineState (globalSourceCode heapSourceProgram) (globalSourceBitmaps heapSourceProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents ∧
    semanticsDecls {sourceTemplate with clock := 0} (ofString "main") heapSourceProgram = .terminate .success finalFfi.ioEvents := by
  obtain ⟨machine,ffi,compilerFinal,compiled,run,events⟩ := machine
  refine ⟨compilerFinal,machine,ffi,compiled,?_,events,?_⟩
  · rw [← clockNumeric]
    exact run
  · rw [events]
    exact sourceSemantics
end SteppedFlapjack.Concrete
