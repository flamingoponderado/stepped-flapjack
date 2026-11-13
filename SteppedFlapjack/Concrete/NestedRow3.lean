import SteppedFlapjack.Concrete.NestedRow3Failure
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem nestedExtract3 : cakeExtractColor (RowColoring.colored nestedRow3) (RowColoring.bij nestedRow3).toAllocator = nestedCols3 := by
  have slots : (RowColoring.colored nestedRow3).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 0)] := by
    decide +kernel
  have bij : (RowColoring.bij nestedRow3).toAllocator = [(0,3),(9,2),(2,1),(5,0)] := by decide +kernel
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,nestedCols3]



end SteppedFlapjack.Concrete
