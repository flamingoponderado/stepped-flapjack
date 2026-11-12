import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.FixtureMachineResults
import SteppedFlapjack.Concrete.BranchingFrames
import SteppedFlapjack.Concrete.FixedWordBounds
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
  simp [branching,evalPanValueFfiProgSteps,panValueIteCondition,panValueReturnResult,evalPanValueExpCounted,
    evalPanValueExp,panValueExpStepCost,comparisonProduction,functionSourceProduction,sourceProduction,
    panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,
    panSemWordModel,RiscV.panRiscVMemoryModel,RiscV.panRiscVCmp]
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

private theorem branch_callee : supportedCallee (progToHOL branchingLoop) = branchingLoopCrepBody := by
  have h := supported_crepPrograms branchingLoop branchingLoop_supported
  rw [branchingLoop_crep_code] at h
  simpa [twoPrograms] using h.symm

private theorem branch_words : supportedWordPrograms branchingLoop = branchWordPrograms := by
  unfold supportedWordPrograms
  rw [branchingLoop_simp_program,branchingLoop_crep_code]
  rfl

private theorem branch_native : (supportedNative branchingLoop).2.2.2 = branchingLoopNativeCode := by
  simp only [supportedNative,supportedAllocated_eq,branch_words,branchingLoopNativeCode]

private theorem branch_frame : supportedCalleeFrame branchingLoop ≤
    (fixtureStack (supportedNative branchingLoop).2.2.2 (fixtureCompilerConfig (supportedNative branchingLoop).2.2.2)).stack.length := by
  let cfg := fixtureCompilerConfig (supportedNative branchingLoop).2.2.2
  have frame := branch_fixture_callee_frame cfg
  change sptLookup 65 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2)) = some 0 at frame
  rw [sptLookupMapi] at frame
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,branch_words]
  cases found : sptLookup 65 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2) with
  | none => simp [found] at frame
  | some pair =>
    obtain ⟨arity,callee⟩ := pair
    simp only [found,Option.map_some,Option.some.injEq] at frame
    dsimp only
    rw [frame]
    exact fixtureStack_nonempty _ _

private theorem branch_crepBudget : supportedCrepBudget branchingLoop 23 = 388 := by
  simp [supportedCrepBudget,branchingLoop_simp_program,branch_callee,branchingLoopCrepBody,CrepSteps.statementWeight]

private theorem branch_loopBudget : supportedLoopBudget branchingLoop 23 = branchLoopBudget := by
  unfold supportedLoopBudget branchLoopBudget
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,conditional_optimized_weight,branch_crepBudget]

private theorem branch_loopVisits : supportedLoopVisits branchingLoop 23 = branchLoopVisits := by
  unfold supportedLoopVisits branchLoopVisits
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,conditional_optimized_weight,branch_crepBudget,branch_loopBudget]

private theorem branch_wordBound : supportedWordBound branchingLoop 23 = branchWordBound := by
  unfold supportedWordBound branchWordBound
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,branch_loopVisits]

private theorem branch_stackBound : supportedStackBound branchingLoop 23 = 348971665463 := by
  unfold supportedStackBound
  rw [branch_words,branch_wordBound]
  change nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms 64
    (loopToWordCompFuncHOL 64 [] branchingLoopEntry) branchWordBound = _
  rw [branch_stackBound_closed,branch_bound_closed]

private theorem branch_ticks : supportedMachineFactor branchingLoop * 23 + supportedMachineOffset branchingLoop = 36771214184170446348 := by
  rw [← supportedMachineTicks_affine]
  unfold supportedMachineTicks
  rw [branch_native,branch_stackBound]
  dsimp only
  rw [branchingLoopLabTick_closed]

/-- The branching-loop witness is an unconditional instance of the Phase 7 theorem. -/
theorem branchingLoopFixture_machine :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL branchingLoop)) = some (fixtureCodeBytes branchingLoopNativeCode,[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart branchingLoopNativeCode)) sourceFfi
      36771214184170446348 (fixtureMachineState branchingLoopNativeCode) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL branchingLoop)).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL branchingLoop)) = .terminate .success ffiPost.ioEvents := by
  have run := branchingLoop_source_run witnessContext witnessPrimitive witnessHandler
  have safe : fixtureStackSafe (supportedNative branchingLoop).2.2.2 = true := by
    rw [branch_native]
    exact branching_stackSafe
  have facts : (fixtureRemoveLabels (supportedNative branchingLoop).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length % 4 = 0 := by
    rw [branch_native]
    exact branching_compiler_facts
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine branchingLoop branchingLoop_supported witnessContext witnessPrimitive witnessHandler 7 23 23
      _ _ _ _ 7 run (by omega) branch_frame safe facts
  rw [branch_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [branch_native] using compiled,
    machinePost,ffiPost,by simpa only [branch_native] using machineRun,events,semantics⟩


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


/-- The prefixed countdown derives its original numerical bound from Phase 7. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL (countdown n))) = some (fixtureCodeBytes (countdownNativeStackCode n),[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600*(6*n+9)+1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL (countdown n))).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL (countdown n))) = .terminate .success ffiPost.ioEvents := by
  obtain ⟨result,_,sourceRun,_,_,resultEq⟩ := countdown_run n range witnessContext witnessPrimitive witnessHandler
  subst result
  have run : evalPanValueFfiProgSteps witnessContext witnessPrimitive witnessHandler (executableState (progToHOL (countdown n))).structs []
      (executableState (progToHOL (countdown n))).baseAddress (executableState (progToHOL (countdown n))).topAddress
      panSemBitVec64BytesInWord (n+4) (executableState (progToHOL (countdown n))).locals
      (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
      (executableState (progToHOL (countdown n))).ffi (countdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (countdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (countdown n))).locals "x"))
          (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
          (executableState (progToHOL (countdown n))).ffi [.word 0],6*n+9) := by
    simpa only [← countdown_hol_eq] using sourceRun
  have safe : fixtureStackSafe (supportedNative (countdown n)).2.2.2 = true := by
    rw [countdown_native]
    exact countdown_stackSafe n
  have facts : (fixtureRemoveLabels (supportedNative (countdown n)).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative (countdown n)).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative (countdown n)).2.2.2).length % 4 = 0 := by
    rw [countdown_native]
    exact countdown_compiler_facts n
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine (countdown n) (countdown_supported n) witnessContext witnessPrimitive witnessHandler
      (n+4) (6*n+9) (6*n+9) _ _ _ _ 0 run (by omega) (countdown_frame n) safe facts
  rw [countdown_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [countdown_native] using compiled,
    machinePost,ffiPost,by simpa only [countdown_native] using machineRun,events,semantics⟩


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
