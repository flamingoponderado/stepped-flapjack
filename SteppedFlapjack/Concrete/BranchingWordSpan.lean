import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Phase 2 clock budget and visit bound for the conditional-loop fixture. -/
def branchLoopBudget : Nat := 240*(388+1)
def branchLoopVisits : Nat := 80*(388+branchLoopBudget+1)+8
/-- Actual two-function Crep and Word code for the branching fixture. -/
def branchCrepCode := twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody
def branchWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa branchCrepCode)
/-- Explicit optimized Word visit bound for the branching fixture. -/
def branchWordBound : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop))
    branchingLoopCrepBody branchLoopVisits phase3WordConfig riscvConfig
end SteppedFlapjack.Concrete
