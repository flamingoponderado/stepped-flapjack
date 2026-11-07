import SteppedFlapjack.Concrete.SourceRuns
import SteppedFlapjack.PanToCrepSteps.SourceInitialFrontend

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
theorem source_globals_related (body : ProgHOL 64)
    (renameEq : fpermHOL (ofString "main") (entryName body) body = body) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState body)
      (callEntryStateHOLFinite (loweredState body) HolFiniteMapExact.empty) := by
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
  apply source_globals_related
  simp [countdownHOL,countdownBodyHOL,fpermHOL]

theorem branching_globals_related :
    panGlobalsStateRelHOLExact true emptyGlobalsContext (exactState branchingHOL)
      (callEntryStateHOLFinite (loweredState branchingHOL) HolFiniteMapExact.empty) := by
  apply source_globals_related
  simp [branchingHOL,fpermHOL]

end SteppedFlapjack.Concrete
