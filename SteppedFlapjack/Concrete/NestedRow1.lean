import SteppedFlapjack.Concrete.NestedRow1Failure
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem nestedExtract1 : cakeExtractColor (RowColoring.colored nestedRow1) (RowColoring.bij nestedRow1).toAllocator = nestedCols1 := by
  have slots : (RowColoring.colored nestedRow1).nodeTag.slots = #[some (.fixed 0),some (.fixed 1),some (.fixed 2),some (.fixed 22),some (.fixed 0)] := by
    decide +kernel
  have bij : (RowColoring.bij nestedRow1).toAllocator = [(0,4),(15,3),(33,2),(2,1),(21,0)] := by decide +kernel
  rw [cakeExtractColor,bij]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort,nestedCols1]


end SteppedFlapjack.Concrete
