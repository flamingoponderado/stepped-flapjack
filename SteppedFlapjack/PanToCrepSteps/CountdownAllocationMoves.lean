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

end SteppedFlapjack.PanToCrepSteps
