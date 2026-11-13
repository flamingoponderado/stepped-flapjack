import SteppedFlapjack.Concrete.CountdownOptimized
import SteppedFlapjack.PanToCrepSteps.CountdownColoring
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.WordToWord SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

namespace SteppedFlapjack.Concrete

/-- The optimized countdown loop for an arbitrary initial count. -/
noncomputable def countdownOptimizedLoop (n : Nat) : WordLangProgHOL (BitVec 64) :=
  ((countdownOptimizedLiteral (BitVec.ofNat 64 n)).get ⟨1,by simp [countdownOptimizedLiteral]⟩).2.2

/-- The optimized entry wrapper tail-calls the countdown loop. -/
def countdownOptimizedEntry : WordLangProgHOL (BitVec 64) :=
  .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none)

end SteppedFlapjack.Concrete
