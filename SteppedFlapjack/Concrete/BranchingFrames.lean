import SteppedFlapjack.Concrete.BranchingNativeInit
import SteppedFlapjack.PanToCrepSteps.RowColoring
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The comparison callee's actual optimized code has no stack frame. -/
theorem comparison_callee_frame : nativeEntryFrameSize countdownZeroLimit
    (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig (comparisonRow,none)).2.2 = 0 := by
  change nativeEntryFrameSize RowColoring.limit (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (_,none)).2.2 = 0
  rw [RowColoring.compiled_exact comparisonRow comparisonColors comparison_guard comparison_failure comparison_extract]
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The branching loop's actual optimized code has no stack frame. -/
theorem branch_callee_frame : nativeEntryFrameSize countdownZeroLimit
    (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig (branchRow,none)).2.2 = 0 := by
  change nativeEntryFrameSize RowColoring.limit (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (_,none)).2.2 = 0
  rw [RowColoring.compiled_exact branchRow branchColors branch_guard branch_failure branch_extract]
  with_unfolding_all rfl
/-- The initialized comparison Word table records the zero callee frame. -/
theorem comparison_fixture_callee_frame (cfg : LabToTarget.Config) :
    sptLookup 65 (comparisonFixtureWord cfg).stackSize = some 0 := by
  change sptLookup 65 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2)) = _
  rw [sptLookupMapi]
  unfold comparisonWordPrograms comparisonCrepCode
  rw [twoProgram_optimized_executable riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody branching_scalar]
  rw [twoLoops_exact riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody (Ne.symm (entryName_fresh branchingHOL))]
  rw [sptLookup_sptFromAList]
  change some (WordToStack.Native.compileProgNative riscvConfig false
    (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig (comparisonRow,none)).2.2
    1 countdownZeroLimit (.nil,0)).2.1 = some 0
  rw [nativeEntryFrameSize_compile]
  exact congrArg some comparison_callee_frame

/-- The initialized branching-loop Word table records the zero callee frame. -/
theorem branch_fixture_callee_frame (cfg : LabToTarget.Config) :
    sptLookup 65 (branchingLoopFixtureWord cfg).stackSize = some 0 := by
  change sptLookup 65 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2)) = _
  rw [sptLookupMapi]
  unfold branchWordPrograms branchCrepCode
  rw [twoProgram_optimized_executable riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody branchingLoop_scalar]
  rw [twoLoops_exact riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop)))]
  rw [sptLookup_sptFromAList]
  change some (WordToStack.Native.compileProgNative riscvConfig false
    (fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig (branchRow,none)).2.2
    1 countdownZeroLimit (.nil,0)).2.1 = some 0
  rw [nativeEntryFrameSize_compile]
  exact congrArg some branch_callee_frame

end SteppedFlapjack.Concrete
