import SteppedFlapjack.WordToStackSteps.EntryComposition

/-! A zero-sized entry allocation cannot take the short allocation-failure path. -/
namespace SteppedFlapjack.StackSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate

/-- If Stack is enabled, a call to a function beginning with `stackAlloc 0`
takes at least four Stack steps. The early allocation-failure path takes at
most three, so it is unreachable for this entry. -/
theorem zeroFrame_entry_steps {C F : Type} (entry : StackSemStateFiniteExact 64 C F)
    (name limit : Nat) (body : HolProg 64)
    (found : sptLookup name entry.code = some (.seq (.stackAlloc 0) body))
    (enabled : entry.useStack = true) :
    4 ≤ steps (.call none (.inl name) none,{entry with clock := limit+1}) := by
  have halloc : evaluate (.stackAlloc 0,{entry with clock := limit}) = (none,{entry with clock := limit}) := by
    rw [evaluate_stackAlloc]
    simp [enabled]
  rw [steps_call_none]
  simp only [findCode,found,Nat.add_one_ne_zero,if_false]
  simp only [decClock,Nat.add_sub_cancel]
  rw [steps_seq,Flapjack.StackSemEvaluateClock.fixClockEvaluate,halloc,
    steps_leaf (.stackAlloc 0) _ rfl]
  simp only
  have positive := steps_pos body {entry with clock := limit}
  omega

end SteppedFlapjack.StackSteps
