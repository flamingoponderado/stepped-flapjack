import SteppedFlapjack.CrepToLoopSteps.ConditionShape
import SteppedFlapjack.CrepToLoopSteps.FrontendScalar
import SteppedFlapjack.Concrete.FrontendShape

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.LoopToWordSteps

/-- The actual source-to-Crep-to-Loop scalar prefix has an explicit,
literal-independent Loop visit bound. -/
theorem sourceScalar_loop_prefix_steps {σ : Type} {scope : List VarName}
    {expression : Exp (RiscV.Word 64)} (scalar : Concrete.Scalar scope expression)
    (panContext : PanToCrepContextExact 64) (registered : Concrete.ScopeRelation scope panContext)
    (loopContext : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact 64 σ) :
    let compiled := (compileExpExactHOLW panContext (expToHOL expression)).1.headD (.const 0)
    let code := (compileExpHOLExact loopContext tmp live compiled).1
    LoopSteps.steps (loopNestedSeqHOL code) state ≤
      LoopSteps.structuralWeight (loopNestedSeqHOL code) := by
  obtain ⟨compiled,compiledEq,shape⟩ := frontendScalar_compiled (Concrete.scalar_frontend_shape registered scalar)
  have bound := compiledScalar_prefix_steps shape loopContext tmp live state
  simpa [compiledEq] using bound

end SteppedFlapjack.CrepToLoopSteps
