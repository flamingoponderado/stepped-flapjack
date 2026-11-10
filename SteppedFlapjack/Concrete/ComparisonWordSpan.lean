import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Phase 2 clock budget and visit bound for the comparison fixture. -/
def comparisonLoopBudget : Nat := 138*(33+1)
def comparisonLoopVisits : Nat := 46*(33+comparisonLoopBudget+1)+8
/-- Actual two-function Crep and Word code for the straight-line branching fixture. -/
def comparisonCrepCode := twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody
def comparisonWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa comparisonCrepCode)
/-- Explicit optimized Word visit bound for the straight-line branching fixture. -/
def comparisonWordBound : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName branchingHOL)
    branchCrepBody comparisonLoopVisits phase3WordConfig riscvConfig
end SteppedFlapjack.Concrete
