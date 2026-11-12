import SteppedFlapjack.CrepToLoopSteps.ScalarPrefix
import SteppedFlapjack.PanToCrepSteps.FrontendScalar

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.LoopToWordSteps

/-- Every frontend scalar, including address expressions and nested comparisons,
produces a Crep scalar whose Loop prefix is supported. -/
theorem frontendScalar_compiled {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {expression : ExpHOL width}
    (scalar : PanToCrepSteps.FrontendScalar ctxt expression) :
    ∃ compiled, compileExpExactHOLW ctxt expression = ([compiled],.one) ∧
      CompiledScalar compiled := by
  induction scalar with
  | const value => exact ⟨.const value,by simp [compileExpExactHOLW],.direct (.const _)⟩
  | «local» name reg found => exact ⟨.var reg,by simp [compileExpExactHOLW,found],.direct (.var _)⟩
  | baseAddr => exact ⟨.baseAddr,by simp [compileExpExactHOLW],.direct .baseAddr⟩
  | topAddr => exact ⟨.topAddr,by simp [compileExpExactHOLW],.direct .topAddr⟩
  | bytesInWord => exact ⟨.const (BitVec.ofNat width (width / 8)),by simp [compileExpExactHOLW],.direct (.const _)⟩
  | fieldLoad index shapes inBounds address ih =>
    obtain ⟨compiled, eq, shape⟩ := ih
    obtain ⟨offset, fieldEq⟩ := PanToCrepSteps.scalarShapeField_compiles ctxt index shapes _ compiled eq inBounds
    refine ⟨_,fieldEq,?_⟩
    split <;> rename_i h
    · exact .load shape
    · exact .load (.op .add shape (.direct (.const _)))
  | load address ih =>
    obtain ⟨compiled, eq, shape⟩ := ih
    exact ⟨.load compiled,by simp [compileExpExactHOLW,eq,sizeOfShapeHOL,loadShapeBytesHOLW],.load shape⟩
  | op operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.op operator [ca,cb],by simp [compileExpExactHOLW,compileExpExactHOLWList,ea,eb,cexpHeads],.op operator ha hb⟩
  | cmp operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.cmp operator ca cb,by simp [compileExpExactHOLW,ea,eb],.cmp operator ha hb⟩
  | shift operator a b iha ihb =>
    obtain ⟨ca,ea,ha⟩ := iha
    obtain ⟨cb,eb,hb⟩ := ihb
    exact ⟨.shift operator ca cb,by simp [compileExpExactHOLW,ea,eb],.shift operator ha hb⟩

end SteppedFlapjack.CrepToLoopSteps
