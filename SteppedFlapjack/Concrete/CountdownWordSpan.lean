import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.CountedApplications
import Flapjack.Compiler.Encoders.RiscV.Target
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- The exact two-function countdown frontend emitted by Phase 1. -/
def phase3CountdownCrepBody (n : Nat) : CrepProgHOL 64 := naturalCountdownCrepBody (BitVec.ofNat 64 n)
def countdownCrepCode (n : Nat) := twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n)
def countdownWordPrograms (n : Nat) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (countdownCrepCode n))
/-- The executable Word-to-Word settings used by the RISC-V backend. -/
def phase3WordConfig : Config := {regAlg := 3, colOracle := []}

theorem phase3WordConfig_eq : phase3WordConfig = countdownRiscVBackend.wordToWordConf := by rfl

end SteppedFlapjack.Concrete
