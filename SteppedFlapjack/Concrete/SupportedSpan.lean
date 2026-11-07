import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! General supported-body source-to-Crep execution bound. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
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

set_option linter.unusedSimpArgs false in
/-- The tail entry used below occurs in the actual generated Crep function list. -/
theorem generated_entry_member (body : ProgHOL 64) :
    (ofString "main",[],.seq .skip (.call none (entryName body) [])) ∈ crepPrograms body := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp_crep_code

/-- Every supported, word-returning callee run lifts through the actual
compiler-generated tail entry with a code-derived bound. The input source run
is at the generated global-lowered callee; connecting it to the counted
original source is a separate remaining obligation. -/
theorem supported_entry_crep_return
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (sourceFinal : PanSemStateFiniteExact 64 Unit) (word : BitVec 64) (sourceLimit : Nat)
    (run : (callEntryStateHOLFinite (loweredState (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
      (progToHOL program) = (some (.returned (.val (.word word))),sourceFinal))
    (sourceBound : controlSteps (progToHOL program)
      (callEntryStateHOLFinite (loweredState (progToHOL program)) HolFiniteMapExact.empty) ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState body) entry = (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepState body) ≤ 3 + sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  let body := progToHOL program
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let pan := callEntryStateHOLFinite (loweredState body) HolFiniteMapExact.empty
  let crep := crepState body
  let target := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
  have relations := supported_callee_relations program supported
  obtain ⟨lookup,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  have span := frontend_correct_with_steps callee body (supported_frontend_shape supported callee)
    pan sourceFinal (some (.returned (.val (.word word)))) target sourceLimit run (by simp) sourceBound
    stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  have returned : targetResult = some (.return [.word word]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,crepState,concreteDeclCrepState,loweredState,noGlobalsLoweredPreCall,
      exactState,singleEntrySourceTemplate,sourceTemplate]
  have wrapper := CrepSteps.tail_entry_returned_word crep (entryName body) (compileProgExactHOLW callee body)
    word targetFinal _ lookup nonzero (by simpa [target,flattenHOL] using targetRun) bound
  exact ⟨targetFinal.emptyLocals,wrapper.1,wrapper.2⟩

end SteppedFlapjack.Concrete
