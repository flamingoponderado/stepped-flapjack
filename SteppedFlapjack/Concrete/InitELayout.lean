import SteppedFlapjack.Concrete.SourceState
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
open Flapjack.Compiler.Backend.StackRemove.Proofs SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete

/-- The real initializer reserves these Stack and semispace word counts. -/
theorem fixture_init_limits :
  InitLimits.getStackHeapLimit (width := 64) (2^61)
    (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd) = (2097172,1944059870) := by
  decide

/-- The fixture is the full reachable semispace, ending inside init-e memory. -/
theorem fixture_heap_end : fixtureHeapEnd = sourceBase + 2*(1944059870*8) := by decide
/-- Each initialized semispace has this byte length. -/
theorem fixture_half_bytes : 1944059870*8 = 0x39efffef0 := by decide

/-- Header offsets agree with one bitmap word and zero extra data words. -/
theorem fixture_bitmap_headers : fixtureHeaders =
  [0xa0020018, 0xa0020018 + 8*(1 : BitVec 64), 0xa0020018 + 8*(1 : BitVec 64), 0x800f0134, 0x800f1000] := by decide

/-- Computing the initializer limit reaches the fixture endpoint exactly. -/
theorem fixture_limit_reaches_end :
  sourceBase + 2 * ((InitLimits.getStackHeapLimit (width := 64) (2^61)
    (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd)).2*8) = fixtureHeapEnd := by
  rw [fixture_init_limits]
  decide

end SteppedFlapjack.Concrete
