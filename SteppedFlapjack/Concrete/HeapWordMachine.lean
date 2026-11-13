import SteppedFlapjack.Concrete.HeapWordNativeFacts
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
import SteppedFlapjack.Concrete.SingletonMachine
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
private theorem compilerDeclEq : globalCompilerDecls heapSourceProgram =
    compileTopExactHOL (declarations (progToHOL heapWordWitness)) (ofString "main") := by
  unfold globalCompilerDecls heapSourceProgram
  rw [simpFunctions]
  change compileTopExactHOL (Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact
    (heapSimpFunctions.map DeclHOL.function)) (ofString "main") = _
  have fixed : Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact (heapSimpFunctions.map DeclHOL.function) = heapSimpFunctions.map DeclHOL.function := by
    exact call_structs_top heapFunctions tableSupported
  rw [fixed,simpDeclarations]
private theorem programsEq : globalSourcePrograms heapSourceProgram = crepPrograms (progToHOL heapWordWitness) := by
  change compileProgDeclsHOLW (globalCompilerDecls heapSourceProgram) = _
  rw [compilerDeclEq]
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
private def ctxt := frontendContext (progToHOL heapWordWitness)
private theorem callFree : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))),heapWordWitness_ranged⟩
private theorem ctxtEq : ctxt = globalCompilerContext heapSourceProgram := by
  unfold ctxt frontendContext globalCompilerContext
  rw [compilerDeclEq]
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
private theorem singletonSourceEq : singletonSourceProgram heapWordWitness = heapSourceProgram := by rfl
private theorem singletonNameEq : singletonName heapWordWitness = name := by
  simp [singletonName,name,simpFixed]
private theorem singletonEntriesEq : singletonEntries heapWordWitness = entries := by
  simp [singletonEntries,entries,singletonNameEq,simpFixed]
private theorem singletonPostEq : singletonPost 1 7 = post := by
  simp [singletonPost,post,sourceTemplateFor_one]
private theorem singletonGlobalsEq : singletonGlobals = globals := by rfl
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
noncomputable def heapUnifiedTicks : Nat :=
  singletonTicks heapWordWitness 1 7
private theorem machine : ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig heapSourceProgram =
      some (fixtureCodeBytes (globalSourceCode heapSourceProgram),globalSourceBitmaps heapSourceProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode heapSourceProgram))) sourceFfi
      heapUnifiedTicks (configuredMachineState (globalSourceCode heapSourceProgram) (globalSourceBitmaps heapSourceProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  have bits : 0xa0020018 + (globalSourceBitmaps heapSourceProgram).length*8 ≤ 0xa0410000 := by rw [bitmaps]; decide
  have bitmapLength : 1 = (globalSourceBitmaps (singletonSourceProgram heapWordWitness)).length := by
    rw [singletonSourceEq,bitmaps]
    rfl
  have normalizedRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
      (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).structs
      (countedFunctionsOfCode (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).code)
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).baseAddress
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).topAddress panSemBitVec64BytesInWord 10
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).locals
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).globals
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).memory
      (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).ffi (panSimpProg heapWordWitness)
      (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness))))
      (contracts := some (countedContractsOfCode (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).code [])) =
        some (.returned (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).locals (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).globals
          (updatePanValueMemory (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).memory 0xa1000100 (.word 7))
          (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).ffi [.word 7],7) := by
    rw [simpFixed]
    with_unfolding_all rfl
  have all := singleton_counted_machine heapWordWitness callFree 1 7 bitmapLength
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 7
    (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).locals (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).globals
    (updatePanValueMemory (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).memory 0xa1000100 (.word 7))
    (globalEntryProduction (singletonPost 1 7) (singletonEntries heapWordWitness)).ffi 7 normalizedRun (by decide)
    (by rw [singletonSourceEq]; exact bits) (by rw [singletonSourceEq]; exact safety)
    (by rw [singletonSourceEq]; exact facts) (by rw [singletonSourceEq]; exact capacity)
  rw [singletonSourceEq] at all
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
  have h := numericTicks heapSourceProgram 7 [] post [] globals entries name ctxt bitmaps optLimit
    (wordWeightOfRaw heapSourceProgram heapWordWitness rawEq wordWeight)
    (stackWeightOfRaw heapSourceProgram heapWordWitness rawEq stackWeight)
    (factorOfRaw heapSourceProgram heapWordWitness rawEq (targetFactor _))
  rw [ctxtEq] at h
  unfold heapUnifiedTicks singletonTicks
  rw [singletonSourceEq,singletonPostEq,singletonEntriesEq,singletonNameEq,singletonGlobalsEq]
  exact h
private def originalProduction := functionSourceProduction heapFunctions 1 7
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
  obtain ⟨final,_,behavior,ffiRel⟩ := singleton_source_semantics heapWordWitness callFree 1 7
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 7
    originalProduction.locals originalProduction.globals
    (updatePanValueMemory originalProduction.memory 0xa1000100 (.word 7)) originalProduction.ffi 7 originalRun (by decide)
  have events : final.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    change FfiEventListRel [] final.ffi.ioEvents at h
    cases heq : final.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  simpa [singletonSourceProgram,singletonFunctions,heapSourceProgram,heapHOLFunctions,heapFunctions,
    sourceTemplateFor_one,sourceFfi,events] using behavior
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
