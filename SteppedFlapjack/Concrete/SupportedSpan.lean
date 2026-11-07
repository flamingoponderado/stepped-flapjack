import SteppedFlapjack.Concrete.CrepError
import SteppedFlapjack.Concrete.CompiledClock
import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.Concrete.GlobalControl
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.PanToCrepSteps.WhileSteps

/-! General supported-body source-to-Crep execution bound. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/-- The actual globals-pass call entry preserves every supported outcome,
including errors, with the generated code table installed. -/
theorem supported_globals_run_from {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (locals : source.locals = HolFiniteMapExact.empty)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) :
    (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
      (progToHOL program) = (result,{sourceFinal with code := (loweredStateFrom source (progToHOL program)).code}) := by
  have entryEq : callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty =
      {source with code := (loweredStateFrom source (progToHOL program)).code} := by
    simp [callEntryStateHOLFinite,loweredStateFrom,noGlobalsLoweredPreCall,locals]
  rw [entryEq]
  have independent := supported_code_irrel supported source (loweredStateFrom source (progToHOL program)).code
  rw [run] at independent
  exact independent

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

/-- A callee that falls through makes the generated tail call report an error. -/
theorem tail_entry_fallthrough {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : MlString) (body : CrepProgHOL width)
    (final : CrepSemHOLState width σ) (limit : Nat)
    (lookup : state.code.lookup name = some ([],body)) (nonzero : state.clock ≠ 0)
    (run : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) body = (none,final))
    (bound : CrepSteps.steps body (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) ≤ limit) :
    evalCrepSemHOLProgExact state (.seq .skip (.call none name [])) = (some .error,final) ∧
    CrepSteps.steps (.seq .skip (.call none name [])) state ≤ 3 + limit := by
  constructor
  · rw [evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
    simp only [if_true]
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp [lookupCodeFiniteHOL,lookup,crepReturnInfoNodupError,nonzero,decClockCrepSemHOL] at run ⊢
    rw [run]
  · rw [CrepSteps.steps_seq]
    simp only [evalCrepSemHOLProgExact_skip]
    rw [CrepSteps.steps_call_tail name [] _ [] [] _ (by simp) lookup (by simp) (by simp) nonzero]
    have one : CrepSteps.steps (.skip : CrepProgHOL width) state = 1 := CrepSteps.steps_leaf _ _ rfl
    rw [one]
    simp only [List.zip, List.zipWith] at bound ⊢
    omega

/-- Outcomes of a supported function body and the corresponding entry result. -/
def bodyExitSource (exit : Option (BitVec 64)) : Option (PanSemResultExact 64) :=
  exit.map (fun word => .returned (.val (.word word)))

def bodyExitEntry (exit : Option (BitVec 64)) : Option (CrepResultHOLExact 64) :=
  match exit with
  | none => some .error
  | some word => some (.return [.word word])

/-- Compile a supported callee and lift either of its non-error exits through the entry. -/
theorem supported_entry_crep_exit_from {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceFinal : PanSemStateFiniteExact 64 σ) (exit : Option (BitVec 64)) (sourceLimit : Nat)
    (run : (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
      (progToHOL program) = (bodyExitSource exit,sourceFinal))
    (sourceBound : controlSteps (progToHOL program)
      (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty) ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom source body) entry = (bodyExitEntry exit,targetFinal) ∧
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
    pan sourceFinal (bodyExitSource exit) target sourceLimit run (by cases exit <;> simp [bodyExitSource]) sourceBound
    stateRel codeRel excpRel localsRel
  obtain ⟨targetResult,targetFinal,targetRun,_,_,_,resultRel,bound⟩ := span
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall]
  cases exit with
  | none =>
    have result : targetResult = none := by
      have h : targetResult = none ∧ panToCrepLocalsRelFiniteExact callee sourceFinal.locals targetFinal.locals := by
        simpa [bodyExitSource,pcCompileCorrectResultRel,flattenHOL] using resultRel
      exact h.1
    subst targetResult
    have wrapper := tail_entry_fallthrough crep (entryName body) (compileProgExactHOLW callee body)
      targetFinal _ lookup nonzero (by simpa [target,flattenHOL] using targetRun) bound
    exact ⟨targetFinal,wrapper.1,wrapper.2⟩
  | some word =>
    have result : targetResult = some (.return [.word word]) := by
      simpa [bodyExitSource,pcCompileCorrectResultRel,flattenHOL] using resultRel
    subst targetResult
    have wrapper := CrepSteps.tail_entry_returned_word crep (entryName body) (compileProgExactHOLW callee body)
      word targetFinal _ lookup nonzero (by simpa [target,flattenHOL] using targetRun) bound
    exact ⟨targetFinal.emptyLocals,wrapper.1,wrapper.2⟩
/-- Lift either supported exit through global lowering and the generated entry. -/
theorem supported_original_entry_crep_exit {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (topOutside : ¬ source.memaddrs source.topAddr) (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one)))
    (exit : Option (BitVec 64)) (sourceLimit : Nat) (run : source.evaluateHOLFiniteState (progToHOL program) = (bodyExitSource exit,sourceFinal))
    (sourceBound : controlSteps (progToHOL program) source ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom source body) entry = (bodyExitEntry exit,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom source body) ≤ 3 + sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  have rel := source_globals_related_from program supported source locals globals structs topOutside aligned sourceCode
  let loweredFinal := {sourceFinal with code := (loweredStateFrom source (progToHOL program)).code}
  have loweredRun := supported_globals_run_from program supported source sourceFinal (bodyExitSource exit) locals run
  have count := supported_globals_control supported emptyGlobalsContext source sourceFinal
    (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty)
    (bodyExitSource exit) run (by cases exit <;> simp [bodyExitSource]) rel
  apply supported_entry_crep_exit_from program supported source locals globals structs exceptions
    loweredFinal exit sourceLimit loweredRun
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
  simpa [loweredStateFrom,crepStateFrom,loweredState,crepState,bodyExitSource,bodyExitEntry] using
    supported_original_entry_crep_exit program supported (exactState (progToHOL program)) sourceFinal
      rfl rfl rfl rfl topOutside aligned code (some word) sourceLimit run sourceBound

/-- Propagate a callee error through the generated tail entry. -/
private theorem tail_entry_error {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ) (name : MlString) (body : CrepProgHOL width)
    (final : CrepSemHOLState width σ) (limit : Nat)
    (lookup : state.code.lookup name = some ([],body)) (nonzero : state.clock ≠ 0)
    (run : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) body =
        (some .error,final))
    (bound : CrepSteps.steps body (decClockCrepSemHOL {state with locals := HolFiniteMapExact.empty.updateList []}) ≤ limit) :
    evalCrepSemHOLProgExact state (.seq .skip (.call none name [])) =
      (some .error,final.emptyLocals) ∧
    CrepSteps.steps (.seq .skip (.call none name [])) state ≤ 3 + limit := by
  constructor
  · rw [evalCrepSemHOLProgExact_seq_holShape,evalCrepSemHOLProgExact_skip]
    simp only [if_true]
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp [lookupCodeFiniteHOL,lookup,crepReturnInfoNodupError,nonzero,decClockCrepSemHOL] at run ⊢
    rw [run]
  · rw [CrepSteps.steps_seq]
    simp only [evalCrepSemHOLProgExact_skip]
    rw [CrepSteps.steps_call_tail name [] _ [] [] _ (by simp) lookup (by simp) (by simp) nonzero]
    have one : CrepSteps.steps (.skip : CrepProgHOL width) state = 1 := CrepSteps.steps_leaf _ _ rfl
    rw [one]
    simp only [List.zip, List.zipWith] at bound ⊢
    omega


theorem supported_entry_crep_error_from {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceFinal : PanSemStateFiniteExact 64 σ) (sourceLimit : Nat)
    (run : (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty).evaluateHOLFiniteState
      (progToHOL program) = (some .error,sourceFinal))
    (sourceBound : controlSteps (progToHOL program)
      (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty) ≤ sourceLimit) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom source body) entry = (some .error,targetFinal) ∧
      CrepSteps.steps entry (crepStateFrom source body) ≤ 3 + 3 * sizeOf (compileProgExactHOLW callee body) * sourceLimit := by
  let body := progToHOL program
  let caller := frontendContext body
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let pan := callEntryStateHOLFinite (loweredStateFrom source body) HolFiniteMapExact.empty
  let crep := crepStateFrom source body
  let target := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
  have relations := supported_callee_relations_from program supported source locals globals structs exceptions
  obtain ⟨lookup,_,stateRel,codeRel,excpRel,localsRel⟩ := relations
  have registered : ScopeRelation [] callee := by intro name member; simp at member
  have present : ScalarScopePresent [] pan := by intro name member; simp at member
  obtain ⟨targetFinal,targetRun,bound⟩ := supported_compiler_error supported.1 callee pan sourceFinal target
    registered present stateRel codeRel excpRel localsRel run
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall]
  have wrapper := tail_entry_error crep (entryName body) (compileProgExactHOLW callee body)
    targetFinal _ lookup nonzero (by simpa [target] using targetRun) bound
  refine ⟨targetFinal.emptyLocals,wrapper.1,?_⟩
  exact wrapper.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ sourceBound) 3)
end SteppedFlapjack.Concrete
