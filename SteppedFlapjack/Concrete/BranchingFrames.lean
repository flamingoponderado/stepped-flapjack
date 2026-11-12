import SteppedFlapjack.Concrete.BranchingNativeInit
import SteppedFlapjack.PanToCrepSteps.RowColoring
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordToStackSteps
namespace SteppedFlapjack.Concrete

private def comparisonRow := (65,1,loopToWordCompFuncHOL 65 []
  (twoCallee riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody))
private def branchRow := (65,1,loopToWordCompFuncHOL 65 []
  (twoCallee riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody))
private def comparisonColors := [(0,0),(2,1),(13,0),(33,1)]
private def branchColors := [(0,0),(2,1),(13,0),(17,1),(21,0),(25,1),(29,1),(33,1),(37,2),(49,1),(61,1),(73,1),(77,1),(93,1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem comparison_guard : countdownAllocatorGuard comparisonRow = true := by with_unfolding_all rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem comparison_failure : (RowColoring.colored comparisonRow).failure = none := by with_unfolding_all rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem comparison_extract : cakeExtractColor (RowColoring.colored comparisonRow) (RowColoring.bij comparisonRow).toAllocator = comparisonColors := by
  have slots : (RowColoring.colored comparisonRow).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij comparisonRow).toAllocator = [(0,3),(33,2),(2,1),(13,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,comparisonColors]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem branch_guard : countdownAllocatorGuard branchRow = true := by with_unfolding_all rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem branch_failure : (RowColoring.colored branchRow).failure = none := by with_unfolding_all rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem branch_extract : cakeExtractColor (RowColoring.colored branchRow) (RowColoring.bij branchRow).toAllocator = branchColors := by
  have slots : (RowColoring.colored branchRow).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 2),some (.fixed 1),some (.fixed 0),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij branchRow).toAllocator = [(0,13),(17,12),(13,11),(29,10),(37,9),(33,8),(61,7),(49,6),(73,5),(77,4),(25,3),(93,2),(2,1),(21,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,branchColors]

private def coloredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))

theorem comparison_optimized_table :
    (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2 =
      [(64,1,countdownOptimizedEntry),(65,1,coloredRow comparisonRow comparisonColors)] := by
  unfold comparisonWordPrograms comparisonCrepCode
  rw [twoProgram_optimized_executable riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody branching_scalar]
  rw [twoLoops_exact riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody (Ne.symm (entryName_fresh branchingHOL))]
  have rows : loopToWordCompileHOL [(64,[],branchingLoopEntry),
      (65,[],twoCallee riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody)] =
      [(64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),comparisonRow] := rfl
  rw [rows]
  simp only [compileWith,show countdownRiscVBackend.wordToWordConf.colOracle = [] by rfl,
    show countdownRiscVBackend.wordToWordConf.regAlg = 3 by rfl]
  have entryEq : loopToWordCompFuncHOL 64 [] branchingLoopEntry = .seq .skip (.seq (.call none (some 65) [0] none) .skip) := by with_unfolding_all rfl
  rw [entryEq]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
      ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (comparisonRow,none)] = _
  rw [countdown_entry_optimized,RowColoring.compiled_exact comparisonRow comparisonColors comparison_guard comparison_failure comparison_extract]
  rfl

theorem branch_optimized_table :
    (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 =
      [(64,1,countdownOptimizedEntry),(65,1,coloredRow branchRow branchColors)] := by
  unfold branchWordPrograms branchCrepCode
  rw [twoProgram_optimized_executable riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody branchingLoop_scalar]
  rw [twoLoops_exact riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop)))]
  have rows : loopToWordCompileHOL [(64,[],branchingLoopEntry),
      (65,[],twoCallee riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody)] =
      [(64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),branchRow] := rfl
  rw [rows]
  simp only [compileWith,show countdownRiscVBackend.wordToWordConf.colOracle = [] by rfl,
    show countdownRiscVBackend.wordToWordConf.regAlg = 3 by rfl]
  have entryEq : loopToWordCompFuncHOL 64 [] branchingLoopEntry = .seq .skip (.seq (.call none (some 65) [0] none) .skip) := by with_unfolding_all rfl
  rw [entryEq]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
      ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (branchRow,none)] = _
  rw [countdown_entry_optimized,RowColoring.compiled_exact branchRow branchColors branch_guard branch_failure branch_extract]
  rfl

end SteppedFlapjack.Concrete
