import SteppedFlapjack.Concrete.FrontendShape
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! General supported-body source-to-Crep execution bound. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

/-- A non-error HOL run of a supported body yields a related Crep run, with
visits bounded by the generated body size times its source control budget.
This is the Pan-to-Crep body pass; it does not yet include the global entry. -/
theorem supported_body_crep_with_steps {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (context : PanToCrepContextExact 64)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (target : CrepSemHOLState 64 σ) (sourceLimit : Nat)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (sourceBound : controlSteps (progToHOL program) source ≤ sourceLimit)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals) :
    ∃ targetResult targetFinal,
      evalCrepSemHOLProgExact target (compileProgExactHOLW context (progToHOL program)) = (targetResult,targetFinal) ∧
      panToCrepStateRelFiniteExact sourceFinal targetFinal ∧
      codeRelExactHOLW context sourceFinal.code targetFinal.code ∧
      panToCrepExcpRelFiniteExact context.eids sourceFinal.eshapes ∧
      pcCompileCorrectResultRel context sourceFinal targetFinal result targetResult ∧
      CrepSteps.steps (compileProgExactHOLW context (progToHOL program)) target ≤
        sizeOf (compileProgExactHOLW context (progToHOL program)) * sourceLimit := by
  exact frontend_correct_with_steps context (progToHOL program) (supported_frontend_shape supported context)
    source sourceFinal result target sourceLimit run nonerror sourceBound stateRel codeRel excpRel localsRel

end SteppedFlapjack.Concrete
