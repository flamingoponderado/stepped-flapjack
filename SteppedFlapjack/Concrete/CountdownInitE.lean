import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordToStack.Native

namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The witness Word table is the original Pancake compiler output. -/
theorem countdown_panToWord (n : Nat) :
    panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL (countdown n))) = countdownWordPrograms n := by
  have h := singleEntry_countdown_panToWord riscvConfig.isa (ofString "x") (BitVec.ofNat 64 n) 0
  have code := natural_countdown_crep_code n
  unfold crepPrograms declarations at code
  dsimp only at h
  simp only [naturalCountdownHOL,naturalCountdown,countdownBody,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil] at code
  rw [code] at h
  simpa [countdownWordPrograms,countdownCrepCode,twoPrograms,phase3CountdownCrepBody, countdown,progToHOL,expToHOL,shapeToHOL,countdownBody,naturalCountdownHOL,naturalCountdown] using h

/-- The original compiler guarantees the countdown Stack table is well formed. -/
theorem countdown_nativeGoodCode (n : Nat) : StackToLab.Proofs.GoodCode.goodCode 24
    (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2 := by
  exact singleEntry_nativeGoodCode (progToHOL (countdown n)) (countdownWordPrograms n) (countdown_panToWord n)

/-- Actual compiled Stack code for the countdown. -/
noncomputable def countdownNativeStackCode (n : Nat) : List (Nat × StackLang.HolProg 64) :=
  (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2

end SteppedFlapjack.Concrete
