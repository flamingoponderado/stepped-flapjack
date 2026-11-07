import SteppedFlapjack.PanToCrepSteps.CountdownAllocation
import Flapjack.Compiler.Backend.RegAlloc.ProductionColourLookup

/-! Exact move preparation for the zero-count allocator input. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.RegAlloc
open Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc

/-- Actual native clash tree and preferences before graph coloring. -/
def countdownZeroClashTree : ClashTree := WordAlloc.getClashTree countdownZeroAllocInput []
def countdownZeroMoves : List (Nat × (Nat × Nat)) :=
  (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).1

/-- Actual node bijection derived from the loop program. -/
def countdownZeroBijection := cakeMkBij (nativeClashTreeToProduction countdownZeroClashTree)

/-- Hash-backed move decoding agrees with the direct association-list lookup.
This equality also covers missing and physical variable names. -/
theorem allocatorIndex_listDecoder (entries : NatInfoMap Nat) :
    cakeAllocatorIndexLookup (cakeAllocatorIndex entries) = CakeAlloc.spDefault entries := by
  funext name
  change cakeSpDefaultIndexed (cakeSpDefaultIndex entries) name = _
  exact spDefaultIndexed_corresponds entries name

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual zero-count loop produces this exact list of allocator-node
moves. This is before move admission and does not assume a coloring. -/
theorem countdownZero_moves_exact :
    countdownZeroMoves.map
      (cakeUpdateMove (cakeAllocatorIndexLookup (cakeAllocatorIndex countdownZeroBijection.toAllocator))) =
    [(12,6,7),(22,3,4),(22,3,5),(12,3,7),(12,3,9),(12,0,8),(12,1,2),(22,8,10)] := by
  rw [allocatorIndex_listDecoder]
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual allocation graph has eleven numbered nodes. -/
theorem countdownZero_bijection_size : countdownZeroBijection.nextNode = 11 := by
  with_unfolding_all rfl

end SteppedFlapjack.PanToCrepSteps
