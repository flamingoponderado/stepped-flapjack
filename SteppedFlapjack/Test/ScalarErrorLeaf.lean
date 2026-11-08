import SteppedFlapjack.Concrete.CrepErrorLeaf
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
example {σ : Type} (ctxt : PanToCrepContextExact 64) (source : PanSemStateFiniteExact 64 σ)
    (target : CrepSemHOLState 64 σ) :
    let expression : Exp (RiscV.Word 64) := .shift .lsl (.const 1) (.const 64)
    evalCrepSemHOLProgExact target (compileProgExactHOLW ctxt (.return (expToHOL expression))) = (some .error,target) ∧
    CrepSteps.steps (compileProgExactHOLW ctxt (.return (expToHOL expression))) target = 1 := by
  apply scalar_return_crep_error (scope := []) (.shift .lsl (.const _) (.const _)) ctxt source target
  · exact ScalarLocalsRel.empty ctxt source target
  · simp [expToHOL,evalHOLExact,wordShiftHOL]
end SteppedFlapjack.Concrete
