import SteppedFlapjack.Concrete.FrontendShape
import Flapjack.Pancake.CrepInline.InlineRouteBridge
import SteppedFlapjack.PanToCrepSteps.SourceInitialFrontend
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations

/-! Concrete frontend states using the compiler's generated function tables. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

def declarations (body : ProgHOL 64) : List (DeclHOL 64) :=
  singleEntryProgram (ofString "main") body

/-- Global lowering generates an entry wrapper and the renamed source function. -/
theorem lowered_declarations (body : ProgHOL 64) :
    compileTopExactHOL (declarations body) (ofString "main") =
      [.function ⟨ofString "main",false,false,[],.seq .skip (.call none (entryName body) []),.one⟩,
       .function ⟨entryName body,false,false,[],
         compileProgExactHOL emptyGlobalsContext (fpermHOL (ofString "main") (entryName body) body),.one⟩] := by
  simpa [declarations,entryName] using singleEntry_compileTop (ofString "main") body

def loweredCode (body : ProgHOL 64) :=
  HolFiniteMapExact.empty.updateList
    (functionsHOL (compileTopExactHOL (declarations body) (ofString "main"))).reverse

def loweredState (body : ProgHOL 64) := noGlobalsLoweredPreCall (exactState body) (loweredCode body)

def crepPrograms (body : ProgHOL 64) := compileProgDeclsHOLW (compileTopExactHOL (declarations body) (ofString "main"))

def crepState (body : ProgHOL 64) := concreteDeclCrepState (loweredState body) (crepPrograms body)

/-- The generated Crep entry has the same machine data as the concrete source. -/
theorem crep_state_related (body : ProgHOL 64) :
    panToCrepStateRelFiniteExact (loweredState body) (crepState body) := by
  apply concreteDecl_panCrep_stateRel <;>
    rfl

/-- Install the generated code while retaining the supplied source machine data. -/
def loweredStateFrom {σ : Type} (source : PanSemStateFiniteExact 64 σ) (body : ProgHOL 64) :=
  noGlobalsLoweredPreCall source (loweredCode body)

def crepStateFrom {σ : Type} (source : PanSemStateFiniteExact 64 σ) (body : ProgHOL 64) :=
  concreteDeclCrepState (loweredStateFrom source body) (crepPrograms body)

/-- Global lowering relates any representable no-global source configuration
to its generated callee, when the original singleton code table is installed. -/
theorem source_globals_related_from {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (entryName (progToHOL program),([],progToHOL program,.one))) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext source
      (callEntryStateHOLFinite (loweredStateFrom source (progToHOL program)) HolFiniteMapExact.empty) := by
  let body := progToHOL program
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body := supported_fperm supported _ _
  apply noGlobals_source_callEntry_rel source (loweredCode body) locals globals structs topOutside aligned
  apply singleEntry_compiled_code_lookup (ofString "main") body source
  change source.code = HolFiniteMapExact.empty.update
    (entryName body,([],fpermHOL (ofString "main") (entryName body) body,.one))
  rw [renameEq]
  exact sourceCode

/-- Renaming-free single-function bodies have a concrete global-lowering relation
using the actual generated function table. -/
theorem source_globals_related (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState (progToHOL program))
      (callEntryStateHOLFinite (loweredState (progToHOL program)) HolFiniteMapExact.empty) := by
  apply source_globals_related_from program supported (exactState (progToHOL program)) rfl rfl rfl
  · simp [exactState,singleEntrySourceTemplate,sourceTemplate,ordinaryAddress,heapTop,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  · change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  · rfl

theorem countdown_globals_related (n : Nat) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState (countdownHOL n))
      (callEntryStateHOLFinite (loweredState (countdownHOL n)) HolFiniteMapExact.empty) := by
  rw [countdown_hol_eq]
  exact source_globals_related (countdown n) (countdown_supported n)

theorem branching_globals_related :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState branchingHOL)
      (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty) := by
  rw [branching_hol_eq]
  exact source_globals_related branching branching_supported

/-- The frontend context selected from the actual global-lowered code. -/
def frontendContext (body : ProgHOL 64) : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (declarations body) (ofString "main")))) 0
    (getEidsFromDeclsHOL (compileTopExactHOL (declarations body) (ofString "main")))

/-- The compiler-generated tables satisfy the exact Pancake-to-Crep code relation
for every supported singleton body. No inliner-shape hypothesis is needed:
the two generated functions are both non-inline. -/
theorem supported_code_related (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    codeRelExactHOLW (frontendContext (progToHOL program))
      (loweredState (progToHOL program)).code (crepState (progToHOL program)).code := by
  let body := progToHOL program
  let declarations' := compileTopExactHOL (declarations body) (ofString "main")
  have sourceUnique : ((functionsHOL declarations').map Prod.fst).Nodup := by
    have unique := singleEntry_compiled_names_unique (ofString "main") body
    rw [compileProgDeclsHOLW,singleEntry_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil] at unique
    simpa [declarations',declarations,compileToCrepExactHOLW,List.map_map,Function.comp_def] using unique
  have localisedBody : localisedProgHOL body = true :=
    frontendProgram_localised (supported_frontend_shape supported (frontendContext body))
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body := supported_fperm supported _ _
  have globalEq : compileProgExactHOL emptyGlobalsContext body = body := supported_globals_fixed supported _
  have localised : ∀ entry ∈ functionsHOL declarations', localisedProgHOL entry.2.2.1 = true := by
    simp only [declarations',declarations,singleEntry_compileTop,functionsHOL,List.mem_cons,List.not_mem_nil,or_false]
    intro entry member
    rcases member with h | h <;> subst entry
    · simp [localisedProgHOL,everyExpListHOL]
    · change localisedProgHOL (compileProgExactHOL emptyGlobalsContext
        (fpermHOL (ofString "main") (entryName body) body)) = true
      rw [renameEq,globalEq]
      exact localisedBody
  have relation := mkCtxtCodeImpCodeRelExactHOLW declarations' sourceUnique localised
  change codeRelExactHOLW (frontendContext body) (loweredState body).code (crepState body).code
  change codeRelExactHOLW _ (HolFiniteMapExact.empty.updateList (functionsHOL declarations').reverse)
    (HolFiniteMapExact.empty.updateList (compileProgDeclsHOLW declarations').reverse)
  change codeRelExactHOLW _ _ (HolFiniteMapExact.empty.updateList
    (CrepInlineCanonical.compileInlTopHOLExact
      ((functionsHOL (declarations'.filter inlinableHOL)).map Prod.fst)
      (compileToCrepExactHOLW declarations')).reverse)
  have noInline : (functionsHOL (declarations'.filter inlinableHOL)).map Prod.fst = [] := by
    exact singleEntry_inline_selection_empty (ofString "main") body
  rw [noInline,CrepInlineRoute.compileInlTopHOLExact_nil]
  exact relation

/-- The generated call supplies the compiled callee and relations for any
source machine state with empty local, global, structure and exception contexts. -/
theorem supported_callee_relations_from {σ : Type}
    (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (exceptions : source.eshapes = HolFiniteMapExact.empty) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let pan := loweredStateFrom source body
    let crep := crepStateFrom source body
    let panEntry := callEntryStateHOLFinite pan HolFiniteMapExact.empty
    let crepEntry := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
    crep.code.lookup (entryName body) = some ([],compileProgExactHOLW callee body) ∧
    localisedProgHOL body = true ∧
    panToCrepStateRelFiniteExact panEntry crepEntry ∧
    codeRelExactHOLW callee panEntry.code crepEntry.code ∧
    panToCrepExcpRelFiniteExact callee.eids panEntry.eshapes ∧
    panToCrepLocalsRelFiniteExact callee panEntry.locals crepEntry.locals := by
  let body := progToHOL program
  let caller := frontendContext body
  let pan := loweredStateFrom source body
  let crep := crepStateFrom source body
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body := supported_fperm supported _ _
  have codeCompiled := singleEntry_compiled_code_lookup (ofString "main") body (exactState body) (by
    change (HolFiniteMapExact.empty : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)).update (entryName body,([],body,.one)) =
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)).update
        (entryName body,([],fpermHOL (ofString "main") (entryName body) body,.one))
    rw [renameEq])
  have codeFound := codeCompiled (entryName body) [] body .one (source_code body)
  have globalEq : compileProgExactHOL emptyGlobalsContext body = body := supported_globals_fixed supported _
  rw [globalEq] at codeFound
  have panFound : pan.code.lookup (entryName body) = some ([],body,.one) := by
    simpa [pan,loweredStateFrom,noGlobalsLoweredPreCall,loweredCode,declarations] using codeFound
  have lookup : lookupCodeHOLFinite pan.code.lookup (entryName body) [] =
      some (body,HolFiniteMapExact.empty,.one) :=
    SemInitSupport.lookup_init _ _ _ _ panFound
  have stateRel : panToCrepStateRelFiniteExact pan crep := by
    apply concreteDecl_panCrep_stateRel
    · simpa [pan,loweredStateFrom,noGlobalsLoweredPreCall] using structs
    · simpa [pan,loweredStateFrom,noGlobalsLoweredPreCall] using globals
  have codeRel : codeRelExactHOLW caller pan.code crep.code := by
    simpa [caller,pan,crep,loweredStateFrom,crepStateFrom,loweredState,crepState,noGlobalsLoweredPreCall,
      concreteDeclCrepState] using supported_code_related program supported
  have excpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes := by
    simpa [caller,frontendContext,pan,loweredStateFrom,noGlobalsLoweredPreCall,exceptions,
      declarations,singleEntry_compiled_eids_empty,mkCtxtExactHOL] using
        (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals := by
    simpa [caller,frontendContext,pan,crep,loweredStateFrom,crepStateFrom,noGlobalsLoweredPreCall,
      concreteDeclCrepState,locals,mkCtxtExactHOL] using
        (empty_panCrep_locals caller crep.locals rfl)
  exact tailEntry_call_relations pan crep caller (entryName body) body HolFiniteMapExact.empty .one
    lookup stateRel codeRel excpRel localsRel


/-- The init-e-shaped fixture instantiates the configurable source-state theorem. -/
theorem supported_callee_relations (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    let body := progToHOL program
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let pan := loweredState body
    let crep := crepState body
    let panEntry := callEntryStateHOLFinite pan HolFiniteMapExact.empty
    let crepEntry := decClockCrepSemHOL {crep with locals := HolFiniteMapExact.empty.updateList []}
    crep.code.lookup (entryName body) = some ([],compileProgExactHOLW callee body) ∧
    localisedProgHOL body = true ∧
    panToCrepStateRelFiniteExact panEntry crepEntry ∧
    codeRelExactHOLW callee panEntry.code crepEntry.code ∧
    panToCrepExcpRelFiniteExact callee.eids panEntry.eshapes ∧
    panToCrepLocalsRelFiniteExact callee panEntry.locals crepEntry.locals := by
  simpa [loweredStateFrom,crepStateFrom,loweredState,crepState] using
    supported_callee_relations_from program supported (exactState (progToHOL program)) rfl rfl rfl rfl

end SteppedFlapjack.Concrete
