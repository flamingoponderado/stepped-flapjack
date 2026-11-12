import SteppedFlapjack.Concrete.NestedRow0
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
deriving instance DecidableEq for CakeNodeTag
def nestedRow1 := (65,1,loopToWordCompFuncHOL 65 [] nestedLoopCode65)
def nestedCols1 := [(0,0),(2,1),(15,22),(21,0),(33,2)]
theorem nestedGuard1 : countdownAllocatorGuard nestedRow1 = true := by decide +kernel

end SteppedFlapjack.Concrete
