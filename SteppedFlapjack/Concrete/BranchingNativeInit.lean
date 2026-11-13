import SteppedFlapjack.Concrete.ComparisonWordSpan
import SteppedFlapjack.Concrete.BranchingWordSpan
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.Concrete.InitEHeap
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.WordAllocSteps.CompiledCodeTail
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
namespace SteppedFlapjack.Concrete

/-- Native Stack code emitted for the comparison witness. -/
noncomputable def comparisonNativeCode :=
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2).2.2.2

/-- Native Stack code emitted for the branching-loop witness. -/
noncomputable def branchingLoopNativeCode :=
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2).2.2.2

open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

end SteppedFlapjack.Concrete
