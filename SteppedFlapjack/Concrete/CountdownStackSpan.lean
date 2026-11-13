import SteppedFlapjack.Concrete.CountdownStackSafety
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.WordToStackSteps.ResourceSafeResult
import SteppedFlapjack.WordToStackSteps.TailFrameBound
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.Concrete

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
