import SteppedFlapjack.Concrete.SourceState
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
open Flapjack.Compiler.Backend.StackRemove.Proofs SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete

/-- The real initializer reserves these Stack and semispace word counts. -/
theorem fixture_init_limits :
  InitLimits.getStackHeapLimit (width := 64) (2^53-1)
    (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd) = (2097172,1944059870) := by
  decide

end SteppedFlapjack.Concrete
