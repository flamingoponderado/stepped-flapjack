import SteppedFlapjack.PanToCrepSteps.SourceFullInitInputs

/-! Canonical matching source environments for a single entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- An empty source environment with one exact HOL function entry. -/
def singleEntrySourceTemplate {σ : Type} (template : PanSemStateFiniteExact 64 σ)
    (entryName : MlString) (body : ProgHOL 64) : PanSemStateFiniteExact 64 σ :=
  {template with
    locals := HolFiniteMapExact.empty
    globals := HolFiniteMapExact.empty
    structs := []
    eshapes := HolFiniteMapExact.empty
    code := HolFiniteMapExact.empty.update (entryName,([],body,.one))}

/-- The matching executable environment, obtained using the exact entry codec. -/
def singleEntrySourceProduction {σ : Type} (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (entryName : MlString) (body : ProgHOL 64) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  {production with
    locals := fun _ => none
    globals := fun _ => none
    structs := []
    exceptionShapes := fun _ => none
    code := [(toStringOfBytes entryName,panLangEntryOfHOL ([],body,.one))]}

/-- The canonical source environments agree on all byte-ranged names. -/
theorem singleEntrySource_environment {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ) (entryName : MlString) (body : ProgHOL 64) :
    PanSemEnvironmentRel (singleEntrySourceProduction production entryName body)
      (singleEntrySourceTemplate template entryName body) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro name ranged
    simp [singleEntrySourceProduction,singleEntrySourceTemplate,HolFiniteMapExact.lookup_empty]
  · intro name ranged
    simp [singleEntrySourceProduction,singleEntrySourceTemplate,HolFiniteMapExact.lookup_empty]
  · rfl
  · intro name ranged
    have keyEq : toStringOfBytes entryName = name ↔ entryName = ofString name := by
      constructor
      · intro h
        simpa [ofString_toStringOfBytes] using congrArg ofString h
      · intro h
        rw [h,toStringOfBytes_ofString_of_bytes name ranged]
    by_cases key : entryName = ofString name
    · simp [singleEntrySourceProduction,singleEntrySourceTemplate,panSemCodeLookup,lookupInfo,
        HolFiniteMapExact.lookup_update,FUPDATE,key,toStringOfBytes_ofString_of_bytes name ranged,panLangEntryToHOL_panLangEntryOfHOL]
    · have ne : toStringOfBytes entryName ≠ name := fun h => key (keyEq.mp h)
      simp [singleEntrySourceProduction,singleEntrySourceTemplate,panSemCodeLookup,lookupInfo,
        HolFiniteMapExact.lookup_update,FUPDATE,ne,key,HolFiniteMapExact.lookup_empty]
  · intro name ranged
    simp [singleEntrySourceProduction,singleEntrySourceTemplate,HolFiniteMapExact.lookup_empty]

/-- The canonical executable environment is byte-ranged independently of the template. -/
theorem singleEntrySource_ranged {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (entryName : MlString) (body : ProgHOL 64) :
    PanSemStateRelExecRanged (singleEntrySourceProduction production entryName body) := by
  simp [PanSemStateRelExecRanged,singleEntrySourceProduction,StructContextByteRanged,StructContext.toHOL]

end SteppedFlapjack.PanToCrepSteps
