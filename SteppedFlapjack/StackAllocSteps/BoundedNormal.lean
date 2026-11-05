import SteppedFlapjack.StackAllocSteps.CollectorStructural
import SteppedFlapjack.StackSteps.AddClock

/-! Transfer bounded normal runs to bounds independent of the initial clock. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackSteps

/-- A normal run at bounded clock transfers a uniform clock bound to any initial clock. -/
theorem stepsOfBoundedNormalRun {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) (K N : Nat)
    (hb : ClockBound (C := C) (F := F) K p N)
    (run : ∃ ck, ck ≤ K ∧ (evaluate (p, {s with clock := ck})).1 = none) :
    steps (p, s) ≤ N := by
  by_cases hs : s.clock ≤ K
  · exact hb s hs
  obtain ⟨ck, hck, hres⟩ := run
  have hle : ck ≤ s.clock := by omega
  let small := {s with clock := ck}
  have heval : evaluate (p, small) = (none, (evaluate (p, small)).2) := by
    apply Prod.ext
    · simpa [small] using hres
    · rfl
  have heq := steps_addClock (s.clock - ck) (stackSemMeasure p small)
    p small rfl none _ heval (by simp)
  have hsteps : steps (p, s) = steps (p, small) := by
    simpa [small, Nat.add_sub_of_le hle] using heq
  rw [hsteps]
  exact hb small (by simpa [small] using hck)

end SteppedFlapjack.StackAllocSteps
