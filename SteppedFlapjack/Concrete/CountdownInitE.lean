import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.InitEHeap
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordToStack.Native

namespace SteppedFlapjack.Concrete

/-- Actual compiled Stack code for the countdown. -/
noncomputable def countdownNativeStackCode (n : Nat) : List (Nat × StackLang.HolProg 64) :=
  (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2

end SteppedFlapjack.Concrete
