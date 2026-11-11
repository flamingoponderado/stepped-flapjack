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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The concrete nested-call machine run follows from compiler and layout checks;
the Lab-to-machine relation is constructed from the initialized machine. -/
theorem nested_initialized_machine
    (capacity : optionLe
      (optionMap₂ max (some (max 1 (1+nestedEntryFrame)))
        (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth nestedFrameSizes 64 (sptFromAList nestedOptimizedWords))))
      (some 2097172))
    (facts : (fixtureRemoveLabels nestedCode).isSome = true ∧
      (fixtureCodeBytes nestedCode).length ≤ 0xecc ∧ (fixtureCodeBytes nestedCode).length % 4 = 0) :
    let rawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let optimized := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig rawWords).2
    let allowance := (max 1 (wordCodeWeight (sptFromAList optimized)) + 1) ^ (6*122+2)
    let n := 1 + max 1 (stackCodeWeight (sptFromAList nestedCode)) * (6*122+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart nestedCode)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          nestedBitmaps nestedCode (fixtureStackOracle (fixtureCompilerConfig nestedCode)) n)
        (configuredMachineState nestedCode nestedBitmaps) = (.halt .success,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = sourceFfi.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplateFor nestedBitmaps.length with clock := 0} (ofString "main")
        (nestedCallDeclarations.map declToHOL) = .terminate .success finalFfi.ioEvents := by
  let cfg := fixtureCompilerConfig nestedCode
  have bitmapFits := nested_bitmapFits
  have safe := nested_nativeSafe
  have fits : 0xa0020018 + nestedBitmaps.length * 8 ≤ sourceBase := by simp only [sourceBase]; omega
  have removed : LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (configuredLab nestedCode cfg nestedBitmaps).code) =
      some ((fixtureCompiled nestedCode).1,(fixtureCompiled nestedCode).2) := fixtureRemoveLabels_eq nestedCode facts.1
  have guards := configuredMachine_allGuards nestedCode nestedBitmaps bitmapFits (nested_labGoodCode _) safe facts
  obtain ⟨filtered,link,tie,rel,buffer⟩ := configuredMachine_relations nestedCode cfg nestedBitmaps bitmapFits
    (fixtureCompiled nestedCode).1 (fixtureCompiled nestedCode).2 nested_nativeGoodCode removed guards
  have result := nested_configured_machine cfg fits capacity filtered (fixtureCodeStart nestedCode)
    (fixtureMachineConfig (fixtureCodeStart nestedCode)) (fixtureCompiled nestedCode).1 (fixtureCompiled nestedCode).2
    (configuredMachineAsm nestedCode nestedBitmaps) (configuredMachineState nestedCode nestedBitmaps) rfl link tie rel
  simp only [buffer, fixtureLabMachineFactor nestedCode facts.2.1] at result
  exact result


end SteppedFlapjack.Concrete
