import SteppedFlapjack.Concrete.NestedMachine
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
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
def nestedRow0 := (64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64)
def nestedCols0 := [(0,0)]
theorem nestedGuard0 : countdownAllocatorGuard nestedRow0 = true := by with_unfolding_all rfl
theorem nestedFailure0 : (RowColoring.colored nestedRow0).failure = none := by with_unfolding_all rfl
theorem nestedExtract0 : cakeExtractColor (RowColoring.colored nestedRow0) (RowColoring.bij nestedRow0).toAllocator = nestedCols0 := by
  have slots : (RowColoring.colored nestedRow0).nodeTag.slots = #[some (.fixed 0)] := by
    apply Array.toList_inj.mp
    with_unfolding_all rfl
  have bij : (RowColoring.bij nestedRow0).toAllocator = [(0,0)] := by with_unfolding_all rfl
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,nestedCols0]

end SteppedFlapjack.Concrete
