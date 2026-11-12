import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.Phase7SourceClock
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps

/-- Byte-representable function names have the same executable and HOL lookup. -/
theorem function_table_lookup (fs : List (FunDeclOf 64))
    (ranged : ∀ f ∈ fs, NameRanged f.name) (name : String) (hn : NameRanged name) :
    Option.map panLangEntryToHOL (panSemCodeLookup (functionEntries (fs.map Decl.function)) name) =
    (HolFiniteMapExact.empty.updateList (functionsHOL ((fs.map (fun f => funDeclToHOL f)).map DeclHOL.function)).reverse).lookup (ofString name) := by
  change Option.map panLangEntryToHOL (panSemCodeLookup (functionEntries (fs.map Decl.function)) name) =
    FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL ((fs.map (fun f => funDeclToHOL f)).map DeclHOL.function)).reverse) (ofString name)
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have hf := ranged f (by simp)
    have ht : ∀ f ∈ fs, NameRanged f.name := fun f h => ranged f (by simp [h])
    by_cases eq : f.name = name
    · subst name
      simp [functionEntries, panSemCodeLookup, lookupInfo, functionsHOL, funDeclToHOL, panLangEntryToHOL]
    · have hne : ofString f.name ≠ ofString name := fun h => eq (ofString_injective_of_ranged hf hn h)
      have hb : (ofString name == ofString f.name) = false := by
        cases he : (ofString name == ofString f.name) <;> simp_all [beq_iff_eq]
      simpa [functionEntries, panSemCodeLookup, lookupInfo, functionsHOL, funDeclToHOL, List.lookup,
        eq, hne, Ne.symm hne, hb, List.map_map] using ih ht


/-- Executable initial state for concrete function declarations and bitmap layout. -/
def functionSourceProduction (fs : List (FunDeclOf 64)) (n clock : Nat) :
    PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {sourceProduction with code := functionEntries (fs.map Decl.function), memory := fun a => some (.word (initialWordFor n a)), clock := clock}

/-- Corresponding HOL initial state for the same declarations and layout. -/
def functionSourceExact (fs : List (FunDeclOf 64)) (n clock : Nat) : PanSemStateFiniteExact 64 Unit :=
  {sourceTemplateFor n with code := HolFiniteMapExact.empty.updateList (functionsHOL ((fs.map funDeclToHOL).map DeclHOL.function)).reverse, clock := clock}

/-- The initialized executable and HOL states agree for every ranged function table. -/
theorem functionSource_related (fs : List (FunDeclOf 64)) (n clock : Nat)
    (ranged : ∀ f ∈ fs, NameRanged f.name) :
    PanSemStateRelExec (functionSourceProduction fs n clock) (functionSourceExact fs n clock).toExact := by
  have base := source_related (.skip : ProgHOL 64)
  obtain ⟨_,_,hs,_,_,_,_,_,_,hbe,hffi,hbase,htop⟩ := base
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,rfl,?_,?_,?_,?_⟩
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simpa [functionSourceProduction,functionSourceExact,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplateFor,sourceTemplate] using hs
  · intro name hname
    exact function_table_lookup fs ranged name hname
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · intro addr member; rfl
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · exact hbe
  · exact hffi
  · exact hbase
  · exact htop


end SteppedFlapjack.Concrete
