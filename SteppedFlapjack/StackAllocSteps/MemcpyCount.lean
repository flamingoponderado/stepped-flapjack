import SteppedFlapjack.StackAllocSteps.Memcpy
import SteppedFlapjack.StackSteps.AddClock
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.Memcpy

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Successful memory copying takes at most twelve steps per copied word,
plus twelve, regardless of the initial clock. -/
theorem memcpyStepsByCount (n : Nat) (a b b1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F)
    (hm : Flapjack.Compiler.Backend.WordGcFunctions.memcpy (BitVec.ofNat width n) a b s.memory s.mdomain = (b1, m1, true))
    (hlt : n < 2 ^ width)
    (h0 : getVar 0 s = some (.word (BitVec.ofNat width n)))
    (h1 : (s.regs.lookup 1).isSome = true)
    (h2 : getVar 2 s = some (.word a)) (h3 : getVar 3 s = some (.word b))
    : steps (memcpyCode, s) ≤ 12 * (n + 1) := by
  by_cases hn : n ≤ s.clock
  swap
  · exact (memcpyStepsLe s).trans (Nat.mul_le_mul_left 12 (by omega))
  let zero := {s with clock := 0}
  obtain ⟨r1, hrun⟩ := memcpyCode_loop n a b b1 m1 zero hm hlt h0 h1 h2 h3
  let small := {s with clock := n}
  have heval : ∃ post, evaluate (memcpyCode, small) = (none, post) := by
    refine ⟨{zero with memory := m1, regs := (zero.regs.updateListEq [(0, .word 0), (1, r1), (2, .word (a + BitVec.ofNat width n * wordSemBytesInWord)), (3, .word b1)])}, ?_⟩
    simpa [zero, small] using hrun
  obtain ⟨post, heval⟩ := heval
  have heq := steps_addClock (s.clock - n) (stackSemMeasure memcpyCode small)
    memcpyCode small rfl none post heval (by simp)
  have hsteps : steps (memcpyCode, s) = steps (memcpyCode, small) := by
    simpa [small, Nat.add_sub_of_le hn] using heq
  rw [hsteps]
  simpa [small] using memcpyStepsLe small

end SteppedFlapjack.StackAllocSteps
