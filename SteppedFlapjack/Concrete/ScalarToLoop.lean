import SteppedFlapjack.CrepToLoopSteps.ConditionShape
import SteppedFlapjack.Concrete.FrontendShape

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.LoopToWordSteps

/-- Every scalar expression accepted by the source fragment compiles to an
expression whose Crep-to-Loop prefix has the generalized shape above. -/
theorem sourceScalar_compiled {scope : List VarName}
    {expression : Exp (RiscV.Word 64)}
    (scalar : Concrete.Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (registered : Concrete.ScopeRelation scope ctxt) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL expression) = ([compiled],.one) ∧
      CompiledScalar compiled := by
  induction scalar with
  | const value =>
    exact ⟨.const value,by simp [expToHOL,compileExpExactHOLW],.direct (.const _)⟩
  | «local» name member =>
    obtain ⟨reg,found⟩ := registered name member
    exact ⟨.var reg,by simp [expToHOL,compileExpExactHOLW,found],.direct (.var _)⟩
  | op operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.op operator [ca,cb],by simp [expToHOL,compileExpExactHOLW,compileExpExactHOLWList,ea,eb,cexpHeads],.op operator ha hb⟩
  | cmp operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.cmp operator ca cb,by simp [expToHOL,compileExpExactHOLW,ea,eb],.cmp operator ha hb⟩
  | shift operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.shift operator ca cb,by simp [expToHOL,compileExpExactHOLW,ea,eb],.shift operator ha hb⟩

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
  obtain ⟨compiled,compiledEq,shape⟩ := sourceScalar_compiled scalar panContext registered
  have bound := compiledScalar_prefix_steps shape loopContext tmp live state
  simpa [compiledEq] using bound

end SteppedFlapjack.CrepToLoopSteps
