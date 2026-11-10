import SteppedFlapjack.Concrete.CountdownStackSafety
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.WordToStackSteps.NativeEntrySpan
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.Concrete

/-- The optimized entry is a supported direct tail call. -/
theorem countdownEntry_shape : RegTailShape countdownOptimizedEntry := by
  apply RegTailShape.seq
  · apply RegTailShape.branch; exact Branch.move 1 [(0,0)]
  · exact RegTailShape.call 65 0

theorem countdownEntry_noInstall : noInstallSubprogsHOL countdownOptimizedEntry = true := by rfl

theorem countdownEntry_flat : flatExpConventions countdownOptimizedEntry = true := by rfl

theorem countdownEntry_convention : postAllocConventionsHOL (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = true := by
  with_unfolding_all rfl

open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The countdown callee requires no native frame space. -/
theorem countdownCallee_entryFrame_zero (n : Nat) :
    nativeEntryFrameSize countdownZeroLimit (countdownOptimizedLoop n) = 0 := by
  simp [nativeEntryFrameSize,nativeFrameSize,nativeFrame,countdownOptimizedLoop,countdownOptimizedLiteral,maxVarHOL,countdownZeroLimit,maxVarInstHOL]
  constructor <;> with_unfolding_all rfl

end SteppedFlapjack.Concrete
