import SteppedFlapjack.StackRemoveSteps.LeafSteps
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect

/-! Statement infrastructure for phase C3 of stepped-flapjack#2: the
step-counted `stack_remove` correctness theorem.

`compCorrectWithinSteps` will conclude, in addition to Flapjack's `compCorrect`,
that the compiled run takes at most `K * steps (program, source)` steps.
The factor `K` must bound `leafCost B bounds` for the current program and
for programs reachable through the code and compile oracle.

The `.storeConsts` expansion depends on the bitmap data accessible at its
run-time state. A bound must apply to the source states actually reached by a
run; `stateRelHOL` does not constrain the target state's `bitmaps` field. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps

variable {width : Nat} [NeZero width] {C F : Type}

/-- Every program reached through `findCode` is reached through a `sptLookup` of
the same code: `findCode` either looks the label up directly (`inl`) or reads a
`loc label 0` from a register (`inr`). This lets the code bound be stated over
`sptLookup` alone and still cover `call` and `jumpLower` targets. -/
theorem findCode_sptLookup {width : Nat} [NeZero width]
    {dest : Sum Nat Nat} {regs : HolFiniteMapExact Nat (WordLocW width)}
    {code : Spt (HolProg width)} {program : HolProg width}
    (h : StackSemControl.findCode dest regs code = some program) :
    ∃ label, sptLookup label code = some program := by
  cases dest with
  | inl label => exact ⟨label, h⟩
  | inr reg =>
    cases lookup : regs.lookup reg with
    | none => simp [StackSemControl.findCode, lookup] at h
    | some value =>
      cases value with
      | loc label offset =>
        cases offset with
        | zero => exact ⟨label, by simpa only [StackSemControl.findCode, lookup] using h⟩
        | succ n => simp [StackSemControl.findCode, lookup] at h
      | word w => simp [StackSemControl.findCode, lookup] at h

end SteppedFlapjack.StackRemoveSteps.CompCorrect
