import SteppedFlapjack.Concrete.NestedRow1
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def nestedRow2 := (66,1,loopToWordCompFuncHOL 66 [] nestedLoopCode66)
def nestedCols2 := [(0,0)]
theorem nestedGuard2 : countdownAllocatorGuard nestedRow2 = true := by with_unfolding_all rfl
theorem nestedFailure2 : (RowColoring.colored nestedRow2).failure = none := by with_unfolding_all rfl
theorem nestedExtract2 : cakeExtractColor (RowColoring.colored nestedRow2) (RowColoring.bij nestedRow2).toAllocator = nestedCols2 := by
  have slots : (RowColoring.colored nestedRow2).nodeTag.slots = #[some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij nestedRow2).toAllocator = [(0,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,nestedCols2]

end SteppedFlapjack.Concrete
