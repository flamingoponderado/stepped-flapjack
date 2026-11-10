import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.CountedApplications
import Flapjack.Compiler.Encoders.RiscV.Target
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- The fixed source fixture satisfies the Word heap-length equation. -/
theorem fixture_heap (program : Prog (RiscV.Word 64)) (fuel : Nat) (body : ProgHOL 64) :
    let source := crepStateFrom (panSimpSourceState program (clockedFixtureSource program fuel)) body
    source.topAddr = source.baseAddr + 2 * fixtureHeapLength := by
  change heapTop = heapBase + 2 * fixtureHeapLength
  decide

/-- Phase 2 clock budget and Loop visit bound for the countdown fixture. -/
def countdownLoopBudget (n : Nat) : Nat := 156*(3 + 8*(6*n+18)+1)
def countdownLoopVisits (n : Nat) : Nat := 52*(3 + 8*(6*n+18)+countdownLoopBudget n+1)+8

/-- The exact two-function countdown frontend emitted by Phase 1. -/
def phase3CountdownCrepBody (n : Nat) : CrepProgHOL 64 := naturalCountdownCrepBody (BitVec.ofNat 64 n)
def countdownCrepCode (n : Nat) := twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n)
def countdownWordPrograms (n : Nat) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (countdownCrepCode n))
/-- The executable Word-to-Word settings used by the RISC-V backend. -/
def phase3WordConfig : Config := {regAlg := 3, colOracle := []}

theorem phase3WordConfig_eq : phase3WordConfig = countdownRiscVBackend.wordToWordConf := by rfl

/-- The explicit optimized Word bound, computed from the compiled functions. -/
def countdownWordBound (n : Nat) : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (countdownLoopVisits n) phase3WordConfig riscvConfig

end SteppedFlapjack.Concrete
