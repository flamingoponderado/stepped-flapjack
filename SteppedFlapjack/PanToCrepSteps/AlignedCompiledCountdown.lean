import SteppedFlapjack.PanToCrepSteps.CountdownGeneralApplication
import SteppedFlapjack.PanToCrepSteps.AlignedLabInitSourceMemory
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards
import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts

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

/-- Byte-addressed heap and bitmap domain before word alignment. -/
noncomputable def countdownStackByteDomain (config : Backend.Config) (asm : AsmState 64)
    (bitmapsDomain : BitVec 64 → Bool) : BitVec 64 → Bool :=
  fun a => decide (asm.regs (StackNames.findNameSpt config.stackConf.regNames 2) ≤ a ∧
    a < asm.regs (StackNames.findNameSpt config.stackConf.regNames 4)) || bitmapsDomain a

end SteppedFlapjack.PanToCrepSteps
