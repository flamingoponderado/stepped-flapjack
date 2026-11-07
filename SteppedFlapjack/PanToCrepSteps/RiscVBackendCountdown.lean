import SteppedFlapjack.PanToCrepSteps.AlignedCompiledCountdown
import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards
import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi

/-! Construct the countdown's matching source environments from an arbitrary template. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps Flapjack.Misc
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

open Flapjack.Compiler.Backend.RiscVConfig

/-- The actual GC-free RISC-V backend used by the Pancake compiler. -/
noncomputable def countdownRiscVBackend : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf riscvBackendConfig

end SteppedFlapjack.PanToCrepSteps
