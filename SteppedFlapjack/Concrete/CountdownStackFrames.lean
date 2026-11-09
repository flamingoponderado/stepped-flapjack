import SteppedFlapjack.Concrete.CountdownOptimized
import SteppedFlapjack.PanToCrepSteps.CountdownZeroFrames

/-! Parameterized frame sizes of the actual countdown Word table. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Both optimized countdown functions have zero-sized native frames. -/
theorem countdown_optimized_frame_sizes (n : Nat) :
    (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2.map
      countdownWordFrameSize = [0,0] := by
  rw [countdown_optimized_literal]
  simp only [countdownOptimizedLiteral,List.map_cons,List.map_nil,countdownWordFrameSize,maxVarHOL]
  with_unfolding_all rfl

/-- Every function in the actual compiled table fits any stack-space budget. -/
theorem countdown_all_frames_fit (n space : Nat) :
    ∀ row ∈ (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2,
      countdownWordFrameSize row ≤ space := by
  intro row member
  have mapped := List.mem_map_of_mem (f := countdownWordFrameSize) member
  rw [countdown_optimized_frame_sizes] at mapped
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mapped
  rcases mapped with h | h <;> omega

end SteppedFlapjack.Concrete
