import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
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

/-- The actual global pass transports a non-error supported source run to
the generated callee for a caller-supplied machine configuration. -/
theorem supported_globals_run_from {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) :
    ∃ targetFinal,
      (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
        (progToHOL program) = (result,targetFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL result) emptyGlobalsContext sourceFinal targetFinal := by
  have related := source_globals_related_from program supported source locals globals structs topOutside aligned sourceCode
  have compiled := PanGlobalsCompileCorrectAssembly.compileCorrectHOL (progToHOL program) source result
    emptyGlobalsContext (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty)
    sourceFinal ⟨related,run,nonerror⟩
  simpa [supported_globals_fixed supported] using compiled

set_option linter.unusedSimpArgs false in
/-- The tail entry used below occurs in the actual generated Crep function list. -/
theorem generated_entry_member (body : ProgHOL 64) :
    (ofString "main",[],.seq .skip (.call none (entryName body) [])) ∈ crepPrograms body := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp_crep_code

/-- For a computed two-function output, the generated table selects its callee. -/
theorem generated_callee_lookup (body : ProgHOL 64) (target : CrepProgHOL 64)
    (code : crepPrograms body =
      [(ofString "main",[],.seq .skip (.call none (entryName body) [])),(entryName body,[],target)]) :
    (crepState body).code.lookup (entryName body) = some ([],target) := by
  have fresh : entryName body ≠ ofString "main" := by
    intro same
    have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
      ((functionsHOL (singleEntryProgram (ofString "main") body)).map Prod.fst)
    apply notMem
    simpa [entryName,newMainNameHOL,singleEntryProgram,functionsHOL] using same
  simp [crepState,concreteDeclCrepState,code,alistToFmapCodeExact,
    HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,Ne.symm fresh]

/-- Every supported, word-returning callee run lifts through the actual
compiler-generated tail entry with a code-derived bound. The input source run
is at the generated global-lowered callee; connecting it to the counted
original source is a separate remaining obligation. -/
theorem supported_entry_crep_return_from {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceFinal : PanSemStateFiniteExact 64 σ) (word : BitVec 64) (sourceLimit : Nat)
    (run : (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
      (progToHOL program) = (some (.returned (.val (.word word))),sourceFinal))
    (sourceBound : controlSteps (progToHOL program)
      (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty) ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom source body) entry = (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom source body) ≤ 3 + sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  let body := progToHOL program
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let pan := callEntryStateHOLFinite (loweredStateFrom source body) HolFiniteMapExact.empty
  let crep := crepStateFrom source body
  let target := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
  have relations := supported_callee_relations_from program supported source locals globals structs exceptions
  obtain ⟨lookup,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  have span := frontend_correct_with_steps callee body (supported_frontend_shape supported callee)
    pan sourceFinal (some (.returned (.val (.word word)))) target sourceLimit run (by simp) sourceBound
    stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  have returned : targetResult = some (.return [.word word]) := by
    simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst targetResult
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall]
  have wrapper := CrepSteps.tail_entry_returned_word crep (entryName body) (compileProgExactHOLW callee body)
    word targetFinal _ lookup nonzero (by simpa [target,flattenHOL] using targetRun) bound
  exact ⟨targetFinal.emptyLocals,wrapper.1,wrapper.2⟩


/-- The init-e-shaped fixture is an instance of the configurable entry theorem. -/
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
  simpa [loweredStateFrom,crepStateFrom,loweredState,crepState] using
    supported_entry_crep_return_from program supported (exactState (progToHOL program)) rfl rfl rfl rfl
      sourceFinal word sourceLimit run sourceBound

end SteppedFlapjack.Concrete
