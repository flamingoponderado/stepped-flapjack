import SteppedFlapjack.Concrete.GlobalStructNativeFacts
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem globalStruct_sourceUnique : ((functionsHOL globalStructProgram).map Prod.fst).Nodup := by
  simp [globalStructProgram,globalStructDecl,functionsHOL,ofString]
def globalStructNativeBitmaps := (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false globalStructOptimizedWords).1

end SteppedFlapjack.Concrete
