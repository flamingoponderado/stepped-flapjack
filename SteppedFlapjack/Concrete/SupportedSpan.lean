import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.Concrete.GlobalControl
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! General supported-body source-to-Crep execution bound. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

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


/-- An original HOL source run lifts through global lowering and the
generated Crep entry, using the original run's control-visit budget. -/
theorem supported_original_entry_crep_return {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (topOutside : ¬ source.memaddrs source.topAddr) (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)))
    (word : BitVec 64) (sourceLimit : Nat)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (some (.returned (.val (.word word))),sourceFinal))
    (sourceBound : controlSteps (progToHOL program) source ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom source body) entry = (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom source body) ≤ 3 + sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  have rel := source_globals_related_from program supported source locals globals structs topOutside aligned sourceCode
  obtain ⟨loweredFinal,loweredRun,_⟩ := supported_globals_run_from program supported source sourceFinal
    (some (.returned (.val (.word word)))) locals globals structs topOutside aligned sourceCode run (by simp)
  have count := supported_globals_control supported emptyGlobalsContext source sourceFinal
    (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty)
    (some (.returned (.val (.word word)))) run (by simp) rel
  apply supported_entry_crep_return_from program supported source locals globals structs exceptions
    loweredFinal word sourceLimit loweredRun
  rw [count]
  exact sourceBound

/-- The original-source entry span instantiated with the checked init-e-shaped fixture. -/
theorem supported_original_entry_crep_return_fixture
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (sourceFinal : PanSemStateFiniteExact 64 Unit) (word : BitVec 64) (sourceLimit : Nat)
    (run : (exactState (progToHOL program)).evaluateHOLFiniteState (progToHOL program) =
      (some (.returned (.val (.word word))),sourceFinal))
    (sourceBound : controlSteps (progToHOL program) (exactState (progToHOL program)) ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState body) entry = (some (.return [.word word]),targetFinal) ∧
      CrepSteps.steps entry (crepState body) ≤ 3 + sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  have topOutside : ¬ (exactState (progToHOL program)).memaddrs (exactState (progToHOL program)).topAddr := by
    simp [exactState,singleEntrySourceTemplate,sourceTemplate,ordinaryAddress,heapTop,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL (exactState (progToHOL program)).topAddr := by
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have code : (exactState (progToHOL program)).code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)) := rfl
  simpa [loweredStateFrom,crepStateFrom,loweredState,crepState] using
    supported_original_entry_crep_return program supported (exactState (progToHOL program)) sourceFinal
      rfl rfl rfl rfl topOutside aligned code word sourceLimit run sourceBound

end SteppedFlapjack.Concrete
