import SteppedFlapjack.CrepToLoopSteps.ExprSequence
import SteppedFlapjack.LoopToWordSteps.SelectedShape

/-! Crep expression programs compile to the selected Loop fragment. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack
open SteppedFlapjack.LoopToWordSteps

/-- The exact Crep compiler emits Loop programs supported by instruction
selection and the quantitative Loop-to-Word proof. -/
theorem compile_exprProgram_select {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : ExprProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live p) := by
  induction shape with
  | leaf leaf =>
    cases leaf <;> simp only [compileHOLExact] <;> exact .leaf (by constructor)
  | returnNil =>
    simp only [compileHOLExact,compileExpsHOLExact,genTemps,List.nil_append]
    exact .seq (.leaf (.ret _)) (.leaf .skip)
  | assign name expr =>
    simp only [compileHOLExact]
    cases ctxt.vars.lookup name with
    | none => exact .leaf .skip
    | some mapped =>
      obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
      simp only [h,List.nil_append,loopNestedSeqHOL]
      exact .seq (.assign _ _) (.leaf .skip)
  | storeGlob name expr =>
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.leaf (.setGlobal _ _)) (.leaf .skip)
  | store dst src =>
    obtain ⟨vd,hd⟩ := directExpression_noCode dst ctxt (ctxt.vmax + 1) live
    obtain ⟨vs,hs⟩ := directExpression_noCode src ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,hd,hs,List.nil_append,loopNestedSeqHOL]
    exact .seq (.assign _ _) (.seq (.store _ _) (.leaf .skip))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using LoopSelectProgram.seq iha ihb

end SteppedFlapjack.CrepToLoopSteps
