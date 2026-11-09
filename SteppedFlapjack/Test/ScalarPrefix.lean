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
/-- The whole loop, not just its condition prefix, accepts nested comparisons. -/
example (ctxt : CrepToLoopContextExact) (live : NumSet) :
    SteppedFlapjack.LoopToWordSteps.LoopSelectProgram
      (compileHOLExact ctxt live (.while nestedComparison .skip)) := by
  have shape : CompiledScalar nestedComparison :=
    .cmp .equal (.cmp .lower (.direct (.const _)) (.direct (.const _))) (.direct (.const _))
  obtain ⟨_,_,_,_,_,_,_,selected⟩ :=
    branchCondition_compileWhile nestedComparison shape .skip (.branch (.expr (.leaf .skip))) ctxt live
  exact selected

/-- Comparisons in a loop body are accepted by the same compiler theorem. -/
example (ctxt : CrepToLoopContextExact) (live : NumSet) :
    SteppedFlapjack.LoopToWordSteps.LoopSelectProgram
      (compileHOLExact ctxt live (.while (.const 1) (.ite nestedComparison .skip .skip))) := by
  have condition : CompiledScalar (.const 1 : CrepExpHOL 64) := .direct (.const _)
  have body : ScalarProgram (.ite nestedComparison .skip .skip) :=
    .ite (.cmp .equal (.cmp .lower (.direct (.const _)) (.direct (.const _))) (.direct (.const _))) .skip .skip
  obtain ⟨_,_,_,_,_,_,_,selected⟩ := branchCondition_compileWhile (.const 1) condition _
    (.scalar body (by rfl)) ctxt live
  exact selected

end SteppedFlapjack.CrepToLoopSteps
