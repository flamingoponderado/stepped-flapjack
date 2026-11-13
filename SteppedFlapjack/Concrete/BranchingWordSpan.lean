import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Actual two-function Crep and Word code for the branching fixture. -/
def branchCrepCode := twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody
def branchWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa branchCrepCode)
end SteppedFlapjack.Concrete
