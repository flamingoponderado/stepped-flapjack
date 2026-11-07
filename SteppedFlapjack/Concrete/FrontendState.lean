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

/-- Renaming-free single-function bodies have a concrete global-lowering relation
using the actual generated function table. -/
theorem source_globals_related (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState (progToHOL program))
      (callEntryStateHOLFinite (loweredState (progToHOL program)) HolFiniteMapExact.empty) := by
  let body := progToHOL program
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body :=
    supported_fperm supported _ _
  change panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState body)
      (callEntryStateHOLFinite (loweredState body) HolFiniteMapExact.empty)
  apply noGlobals_source_callEntry_rel (exactState body) (loweredCode body)
  · rfl
  · rfl
  · rfl
  · simp [exactState,singleEntrySourceTemplate,sourceTemplate,ordinaryAddress,heapTop,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  · change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  · apply singleEntry_compiled_code_lookup (ofString "main") body (exactState body)
    change (HolFiniteMapExact.empty : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)).update (entryName body,([],body,.one)) =
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)).update (entryName body,([],fpermHOL (ofString "main") (entryName body) body,.one))
    rw [renameEq]

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

/-- The generated zero-argument call supplies the actual compiled callee and
all Pancake-to-Crep relations, for any supported source body. -/
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
  let body := progToHOL program
  let caller := frontendContext body
  let pan := loweredState body
  let crep := crepState body
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
    simpa [pan,loweredState,noGlobalsLoweredPreCall,loweredCode,declarations] using codeFound
  have lookup : lookupCodeHOLFinite pan.code.lookup (entryName body) [] =
      some (body,HolFiniteMapExact.empty,.one) :=
    SemInitSupport.lookup_init _ _ _ _ panFound
  have stateRel : panToCrepStateRelFiniteExact pan crep := crep_state_related body
  have codeRel : codeRelExactHOLW caller pan.code crep.code := supported_code_related program supported
  have excpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes := by
    simpa [caller,frontendContext,pan,loweredState,noGlobalsLoweredPreCall,exactState,
      singleEntrySourceTemplate,sourceTemplate,declarations,singleEntry_compiled_eids_empty,mkCtxtExactHOL] using
        (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals := by
    simpa [caller,frontendContext,pan,loweredState,noGlobalsLoweredPreCall,exactState,
      singleEntrySourceTemplate,sourceTemplate,mkCtxtExactHOL] using
        (empty_panCrep_locals caller crep.locals rfl)
  exact tailEntry_call_relations pan crep caller (entryName body) body HolFiniteMapExact.empty .one
    lookup stateRel codeRel excpRel localsRel

end SteppedFlapjack.Concrete
