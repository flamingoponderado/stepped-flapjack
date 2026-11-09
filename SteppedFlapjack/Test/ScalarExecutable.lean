import SteppedFlapjack.CrepToLoopSteps.ScalarExecutable

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack

/-- The executable path computes the actual optimizer on nested loops. -/
example : optimiseHOL
    (HolLoopProg.loop .ln (.loop .ln (.break 0) .ln) .ln : HolLoopProg 64) =
    .loop .ln (.loop .ln (.mark (.break 0)) .ln) .ln := by
  have shape : ScalarLoop (HolLoopProg.loop .ln (.loop .ln (.break 0) .ln) .ln : HolLoopProg 64) :=
    .loop _ _ (.loop _ _ (.branch (.break 0)))
  rw [← optimiseScalar_eq shape]
  simp [optimiseScalar,scalarDepth,shrinkScalar,scalarFixedpoint,
    SteppedFlapjack.LoopLiveSteps.shrinkBranch,markAllHOL,sptInter,sptUnion,sptOel]

end SteppedFlapjack.CrepToLoopSteps
