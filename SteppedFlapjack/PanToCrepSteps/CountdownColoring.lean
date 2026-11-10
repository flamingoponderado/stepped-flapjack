import SteppedFlapjack.PanToCrepSteps.CountdownAllocationMoves
import SteppedFlapjack.PanToCrepSteps.RowColoring

/-! Staged graph coloring for the actual zero-count loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc
open SteppedFlapjack.RegAllocSteps

def countdownZeroForced := RowColoring.forced countdownZeroLoopRow
def countdownZeroLimit := RowColoring.limit
def countdownZeroColored := RowColoring.colored countdownZeroLoopRow

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete coloring pass produces these exact node tags. -/
theorem countdownZero_colored_tags : countdownZeroColored.nodeTag.slots.toList =
    [some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),
      some (.fixed 1),some (.fixed 1),some (.fixed 0),some (.fixed 1),some (.fixed 0)] := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete graph-coloring run does not report failure. -/
theorem countdownZero_colored_no_failure : countdownZeroColored.failure = none := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual source-to-allocator node numbering. -/
theorem countdownZero_bijection_exact : countdownZeroBijection.toAllocator =
    [(0,10),(13,9),(9,8),(25,7),(29,6),(33,5),(41,4),(21,3),(53,2),(2,1),(17,0)] := by
  with_unfolding_all rfl

/-- The extracted colors of the actual zero-count allocation. -/
theorem countdownZero_extracted_colors : cakeExtractColor countdownZeroColored countdownZeroBijection.toAllocator =
    [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)] := by
  have slots : countdownZeroColored.nodeTag.slots =
      #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),
        some (.fixed 1),some (.fixed 1),some (.fixed 0),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    exact countdownZero_colored_tags
  rw [cakeExtractColor,countdownZero_bijection_exact]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort]

/-- The executable allocator returns this exact coloring for the actual
zero-count loop function. -/
theorem countdownZero_graphAllocation_exact :
    regAllocExecutable .IRC
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).2
      countdownZeroLimit countdownZeroMoves countdownZeroClashTree countdownZeroForced
      (WordAlloc.getStackOnly countdownZeroAllocInput) =
    .success (sptFromAList [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)]) := by
  have guard := countdown_zero_allocator_guard
  rw [countdownZeroLoopRow_from_compiler] at guard
  have accepted : countdownAllocatorGuard countdownZeroLoopRow = true := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,true_and,and_true] using guard
  exact RowColoring.graphAllocation_exact countdownZeroLoopRow _ accepted
    countdownZero_colored_no_failure countdownZero_extracted_colors

/-- The exact register coloring computed by the graph allocator. -/
def countdownZeroColor : Spt Nat :=
  sptFromAList [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)]

end SteppedFlapjack.PanToCrepSteps
