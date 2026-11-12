import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.NestedMachine
import SteppedFlapjack.PanToCrepSteps.RowColoring
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def row0 := (64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64)
private def cols0 := [(0,0)]
private theorem guard0 : countdownAllocatorGuard row0 = true := by with_unfolding_all rfl
private theorem failure0 : (RowColoring.colored row0).failure = none := by with_unfolding_all rfl
private theorem extract0 : cakeExtractColor (RowColoring.colored row0) (RowColoring.bij row0).toAllocator = cols0 := by
  have slots : (RowColoring.colored row0).nodeTag.slots = #[some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row0).toAllocator = [(0,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,cols0]
private def row1 := (65,1,loopToWordCompFuncHOL 65 [] nestedLoopCode65)
private def cols1 := [(0,0),(2,1),(15,22),(21,0),(33,2)]
private theorem guard1 : countdownAllocatorGuard row1 = true := by with_unfolding_all rfl
private theorem failure1 : (RowColoring.colored row1).failure = none := by with_unfolding_all rfl
private theorem extract1 : cakeExtractColor (RowColoring.colored row1) (RowColoring.bij row1).toAllocator = cols1 := by
  have slots : (RowColoring.colored row1).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 2),some (.fixed 22),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row1).toAllocator = [(0,4),(15,3),(33,2),(2,1),(21,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols1]
private def row2 := (66,1,loopToWordCompFuncHOL 66 [] nestedLoopCode66)
private def cols2 := [(0,0)]
private theorem guard2 : countdownAllocatorGuard row2 = true := by with_unfolding_all rfl
private theorem failure2 : (RowColoring.colored row2).failure = none := by with_unfolding_all rfl
private theorem extract2 : cakeExtractColor (RowColoring.colored row2) (RowColoring.bij row2).toAllocator = cols2 := by
  have slots : (RowColoring.colored row2).nodeTag.slots = #[some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row2).toAllocator = [(0,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,cols2]
private def row3 := (67,1,loopToWordCompFuncHOL 67 [] nestedLoopCode67)
private def cols3 := [(0,0),(2,1),(5,0),(9,1)]
private theorem guard3 : countdownAllocatorGuard row3 = true := by with_unfolding_all rfl
private theorem failure3 : (RowColoring.colored row3).failure = none := by with_unfolding_all rfl
private theorem extract3 : cakeExtractColor (RowColoring.colored row3) (RowColoring.bij row3).toAllocator = cols3 := by
  have slots : (RowColoring.colored row3).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij row3).toAllocator = [(0,3),(9,2),(2,1),(5,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,cols3]

private def coloredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))

theorem nested_optimizedTable : nestedOptimizedWords =
  [(64,1,coloredRow row0 cols0),(65,1,coloredRow row1 cols1),
   (66,1,coloredRow row2 cols2),(67,1,coloredRow row3 cols3)] := by
  unfold nestedOptimizedWords nestedRawWords
  rw [nestedCall_loop_code]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row0,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row1,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row2,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (row3,none)] = _
  rw [RowColoring.compiled_exact row0 cols0 guard0 failure0 extract0,
    RowColoring.compiled_exact row1 cols1 guard1 failure1 extract1,
    RowColoring.compiled_exact row2 cols2 guard2 failure2 extract2,
    RowColoring.compiled_exact row3 cols3 guard3 failure3 extract3]
  rfl

theorem nested_bitmaps : nestedBitmaps = [4,2] := by
  unfold nestedBitmaps nestedNative
  rw [nested_optimizedTable]
  with_unfolding_all rfl

theorem nested_frames : nestedFrameSizes = sptFromAList [(64,0),(65,2),(66,0),(67,0)] := by
  unfold nestedFrameSizes
  rw [nested_optimizedTable]
  with_unfolding_all rfl

theorem nested_bitmapFits : 0xa0020018 + nestedBitmaps.length * 8 ≤ 0xa0410000 := by
  rw [nested_bitmaps]
  decide

theorem nested_entryFrame : nestedEntryFrame = 0 := by
  unfold nestedEntryFrame nestedEntry
  rw [nested_optimizedTable]
  with_unfolding_all rfl

theorem nested_nativeSafe : fixtureStackSafe nestedCode = true := by
  unfold nestedCode nestedNative
  rw [nested_optimizedTable]
  with_unfolding_all rfl

private theorem row0_exact : coloredRow row0 cols0 =
    .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none) := by with_unfolding_all rfl
private theorem row1_exact : coloredRow row1 cols1 =
    .seq (.move 1 [(44,0)])
      (.seq (.call (some ([2], ((Spt.ln.bn (((Spt.ln.bn (Spt.ls PUnit.unit)).bn Spt.ln).bn Spt.ln)).bn Spt.ln, Spt.ln),
        .move 1 [(4,2),(0,44)],65,2)) (some 66) []
        (some (2,.seq (.move 1 [(2,2),(0,44)]) (.raise 2),65,3)))
        (.seq .tick (.seq (.move 0 [(2,4)]) (.return 0 [2])))) := by with_unfolding_all rfl
private theorem row2_exact : coloredRow row2 cols2 =
    .seq (.move 1 [(0,0)]) (.call none (some 67) [0] none) := by with_unfolding_all rfl
private theorem row3_exact : coloredRow row3 cols3 =
    .seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 (7 : BitVec 64)))
      (.seq (.move 0 [(2,2)]) (.return 0 [2]))) := by with_unfolding_all rfl

set_option maxHeartbeats 3000000 in
theorem nested_callDepth : Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth
    nestedFrameSizes 64 (sptFromAList nestedOptimizedWords) = some 5 := by
  rw [nested_frames, nested_optimizedTable, row0_exact, row1_exact, row2_exact, row3_exact]
  simp [Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth,
    Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptLookup_sptFromAList, sptAListLookup]
  split <;> simp_all [sptLookup_sptFromAList, sptAListLookup]
  all_goals obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›
  all_goals simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptSize, sptFromAList, sptInsert]
  all_goals split <;> simp_all [sptLookup]
  all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
  all_goals simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth, sptDelete]
  all_goals split <;> simp_all [sptLookup, sptMkBN]
  all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
  all_goals try simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth]
  all_goals with_unfolding_all rfl

theorem nested_capacity : optionLe
    (optionMap₂ max (some (max 1 (1+nestedEntryFrame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth nestedFrameSizes 64 (sptFromAList nestedOptimizedWords))))
    (some 2097172) := by
  rw [nested_entryFrame, nested_callDepth]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nested_compilerFacts : (fixtureRemoveLabels nestedCode).isSome = true ∧
    (fixtureCodeBytes nestedCode).length ≤ 0xecc ∧ (fixtureCodeBytes nestedCode).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels nestedCode nestedNative
    rw [nested_optimizedTable, row0_exact, row1_exact, row2_exact, row3_exact]
    with_unfolding_all decide
  · unfold fixtureCodeBytes nestedCode nestedNative
    rw [nested_optimizedTable, row0_exact, row1_exact, row2_exact, row3_exact]
    simp_rw [LabToTarget.progToBytesMap]
    with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The concrete nested-call machine run follows from compiler and layout checks;
the Lab-to-machine relation is constructed from the initialized machine. -/
theorem nested_initialized_machine :
    let rawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig rawWords).2
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) * (6*nestedOptimizedLoopBound+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList nestedCode)) * (6*nestedOptimizedLoopBound+1 + allowance)
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (nestedCallDeclarations.map declToHOL) = some (fixtureCodeBytes nestedCode,[4,2],compilerFinal) ∧
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart nestedCode)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          [4,2] nestedCode (fixtureStackOracle (fixtureCompilerConfig nestedCode)) n)
        (configuredMachineState nestedCode [4,2]) = (.halt .success,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = sourceFfi.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplateFor 2 with clock := 0} (ofString "main")
        (nestedCallDeclarations.map declToHOL) = .terminate .success finalFfi.ioEvents := by
  let n := nestedBitmaps.length
  let source := {nestedSourceState n with clock := 6}
  let memory : BitVec 64 → Option (PanValue (RiscV.Word 64)) := fun a => some (.word (initialWordFor n a))
  let production := {nestedCountedProduction with clock := 6, memory := memory}
  let _ : DecidablePred source.memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  have shape : CallSupportedIn [] nestedCallEntry :=
    .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  have sourceCode : source.code = HolFiniteMapExact.empty.updateList (functionsHOL (nestedCallDeclarations.map declToHOL)).reverse := by
    exact nestedEntryCode
  have sourceRun := nestedCounted_run memory (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  have unique : ((functionsHOL (nestedCallDeclarations.map declToHOL)).map Prod.fst).Nodup := by
    simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL]
    decide
  have span := countedCalls_initializedMachine ⟨shape, by simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]⟩ production source nestedSourceFunctions n 6 nested_table_supported
    (by rfl) (by simpa [source] using (nestedSourceExact_eq n 6).symm)
    source.code
    (functionsHOL (nestedCallDeclarations.map declToHOL)) (by rfl)
    nestedHOLFunctions (by simp [nestedHOLFunctions,nestedSourceFunctions,nestedCallEntry,funDeclToHOL,progToHOL,expToHOL,shapeToHOL])
    (by simpa only [nestedHOLDeclarations] using unique)
    nestedHOLFunctions (by simp [nestedHOLFunctions,nestedCallEntry,progToHOL,expToHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL]) (ofString "main") rfl
    (by simpa only [nestedHOLDeclarations] using sourceCode)
    (by simp [source,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE,ofString])
    (by simpa only [nestedHOLDeclarations] using nestedCall_inline_selection_empty)
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 8 6
    _ _ _ _ 7 (by simpa [production,panSemBitVec64MemoryAccess] using sourceRun) (by rfl)
    (by simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedRawWords,nestedOptimizedWords,nestedNative,nestedBitmaps] using nested_bitmapFits)
    (by simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedRawWords,nestedOptimizedWords,nestedNative,nestedCode] using nested_nativeSafe)
    (by simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedRawWords,nestedOptimizedWords,nestedNative,nestedCode] using nested_compilerFacts)
    (by simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedRawWords,nestedOptimizedWords,nestedNative,
      nestedEntry,nestedEntryFrame,nestedFrameSizes] using nested_capacity)
    (by
      dsimp only
      rw [nestedHOLDeclarations]
      change nestedBitmaps.length = nestedBitmaps.length
      rfl)
  obtain ⟨sourceFinal,finalMachine,finalFfi,compilerFinal,compiled,sourceResult,machineRun,events,ffiRel,semantics⟩ := span
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [nestedCountedProduction,sourceProduction,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  have outputEvents : finalFfi.ioEvents = sourceFfi.ioEvents := by
    simpa [sourceFfi,sourceEvents] using events
  rw [nestedHOLDeclarations] at machineRun semantics
  have codeWeight : CrepSteps.codeWeight (compileProgDeclsHOLW
      (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))) = 4 := by
    rw [nestedCall_crep_code]
    rfl
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
    CrepSteps.statementWeight,codeWeight,show max 3 4 = 4 by decide] at machineRun
  have fresh : newMainNameHOL (nestedCallDeclarations.map declToHOL) = ofString "main'" := by
    simp [newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,
      ofString,MlString.explode_implode]
  simp only [source,nestedSourceState,sourceTemplateFor,sourceTemplate,concreteDeclCrepState,noGlobalsLoweredPreCall,
    concreteDeclLoopState,fresh] at machineRun
  rw [nestedHOLDeclarations, ← nestedCallCrepPrograms, ← nestedRawWords, ← nestedOptimizedWords,
    ← nestedNative, ← nestedCode, ← nestedBitmaps, nested_bitmaps] at compiled
  refine ⟨compilerFinal,compiled,finalMachine,finalFfi,?_,outputEvents,?_⟩
  · unfold callPipelineTicks at machineRun
    simp only [List.flatMap_nil,Nat.reduceAdd] at machineRun
    rw [← nestedCallCrepPrograms, ← nestedRawWords, ← nestedOptimizedWords, ← nestedNative,
      ← nestedCode, ← nestedBitmaps] at machineRun
    have bodyEq : (CrepProgHOL.skip.seq (CrepProgHOL.call none (ofString "main'") []) : CrepProgHOL 64) = nestedCrepBody := by
      simp [nestedCrepBody,nestedPanContext,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
    rw [bodyEq, ← nestedLoopContext] at machineRun
    have entryEq : 1 + (SimpVisits.simpTableFactor (functionsHOL (nestedCallDeclarations.map declToHOL)) * 6 +
        SimpVisits.hw (progToHOL (panSimpProg nestedCallEntry))) + 2 = nestedSourceEntryLimit := by
      simp [nestedSourceEntryLimit,Nat.add_assoc]
    rw [entryEq, ← nestedCrepLimit, ← nestedLoopBudget, ← nestedLoopBound,
      ← nestedOptimizedLoopBody, ← nestedOptimizedLoopBound] at machineRun
    rw [nested_bitmaps] at machineRun
    simpa only [nestedOptimizedWords,nestedRawWords] using machineRun
  · simpa [source,n,nestedSourceState,sourceTemplateFor,sourceTemplate,nested_bitmaps] using semantics

end SteppedFlapjack.Concrete
