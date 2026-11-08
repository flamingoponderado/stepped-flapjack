import SteppedFlapjack.CrepToLoopSteps.ConditionShape
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact

def nestedComparison : CrepExpHOL 64 :=
  .cmp .equal (.cmp .lower (.const 1) (.const 2)) (.const 1)

example {σ : Type} (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 σ) :
    LoopSteps.steps (loopNestedSeqHOL (compileExpHOLExact ctxt tmp live nestedComparison).1) state ≤ 17 := by
  have shape : CompiledScalar nestedComparison :=
    .cmp .equal (.cmp .lower (.direct (.const _)) (.direct (.const _))) (.direct (.const _))
  have bound := compiledScalar_prefix_steps shape ctxt tmp live state
  simpa [nestedComparison,compileExpHOLExact,progIfHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight] using bound
end SteppedFlapjack.CrepToLoopSteps
