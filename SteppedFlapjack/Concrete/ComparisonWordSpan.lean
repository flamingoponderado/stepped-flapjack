import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Actual two-function Crep and Word code for the straight-line branching fixture. -/
def comparisonCrepCode := twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody
def comparisonWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa comparisonCrepCode)
end SteppedFlapjack.Concrete
