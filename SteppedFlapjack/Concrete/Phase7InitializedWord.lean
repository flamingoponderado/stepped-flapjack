import SteppedFlapjack.Concrete.Phase7Frontend
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.FixtureMachineGuards

/-! Supported programs in the actual initialized native backend. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

def supportedWordPrograms (program : Prog (RiscV.Word 64)) :=
  loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL (panSimpProg program))))

def supportedAllocated (program : Prog (RiscV.Word 64)) :=
  Flapjack.Compiler.Backend.WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (supportedWordPrograms program)

def supportedNative (program : Prog (RiscV.Word 64)) :=
  WordToStack.Native.compileNative riscvConfig false (supportedAllocated program).2

end SteppedFlapjack.Concrete
