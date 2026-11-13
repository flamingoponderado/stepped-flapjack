import SteppedFlapjack.PanToCrepSteps.GlobalInitializedEntry
import SteppedFlapjack.Concrete.GlobalStructInitializer
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def decl : DeclHOL 64 := .decl (.comb [.one,.one]) (ofString "pair") (.rstruct [.const 3,.const 4])
private def body : ProgHOL 64 := .return (.rfield 1 (.var .global (ofString "pair")))
private def entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) := [(ofString "entry",[],body,ShapeHOL.one)]
private def template := {globalStructTarget with clock := 8}
private def target := installTargetFunctions template globalStructContext entries
private def base := beforeGlobals target 16 2
private def post := setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 3,.word 4])) base
private def source := callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty
private def final := emptyLocalsHOLFinite source
private theorem declEval : @evaluateDeclsHOLFinite 64 Unit _ base (fun _a => Classical.propDecidable _) [decl] = some post := by
  with_unfolding_all rfl
private theorem shape : GlobalCallFrontend globalStructContext globalStructCrepContext body := by
  exact .base (.ret (.globalField (ofString "pair") 16 1 [.one,.one] (by rfl) globalStruct_pairLookup))
private theorem sourceRun : source.evaluateHOLFiniteState body = (some (.returned (.val (.word 4))),final) := by
  simp [source,body,final,post,base,callEntryStateHOLFinite,installSourceFunctions,
    setGlobalHOLFinite,evaluateHOLFiniteState_return,evalHOLExact,
    FUPDATE,emptyLocalsHOLFinite,shapeOfHOLExact]

private theorem sourceBound : controlSteps body source ≤ 1 := by
  rw [controlSteps.eq_def]
  rfl
private theorem table : GlobalCallTable globalStructContext source.code := by
  intro name values fn locals ret found
  have raw := lookupCodeHOLFinite_eq_some source.code.lookup name values fn locals ret found
  by_cases eq : name = ofString "entry"
  · subst name
    cases values with
    | nil =>
      simp [lookupCodeHOLExact,source,callEntryStateHOLFinite,installSourceFunctions,entries,
        HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE] at raw
      obtain ⟨rfl,_,_⟩ := raw
      exact ⟨globalStructCrepContext,shape⟩
    | cons v vs =>
      simp [lookupCodeHOLExact,source,callEntryStateHOLFinite,installSourceFunctions,entries,
        HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE] at raw
  · simp [lookupCodeHOLExact,source,callEntryStateHOLFinite,installSourceFunctions,entries,
      HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,HolFiniteMapExact.lookup_empty,Ne.symm eq] at raw
private theorem allocated : ∀ a, addresses (template.topAddr - 16) 2 a → template.memaddrs a := by
  simpa [template] using globalStructSlots_allocated
/-- Initializing the pair to (3, 4) makes the generated entry return 4. -/
theorem nonzeroGlobal_entry : ∃ targetFinal, target.evaluateHOLFiniteState
    (.seq (nestedSeqHOL (compileDecsExactHOL globalStructStart [decl]).1) (.call none (ofString "entry") [])) =
      (some (.returned (.val (.word 4))),emptyLocalsHOLFinite targetFinal) := by
  have compiled : compileDecsExactHOL globalStructStart [decl] =
    ((compileDecsExactHOL globalStructStart [decl]).1,
     (compileDecsExactHOL globalStructStart [decl]).2.1,
     (compileDecsExactHOL globalStructStart [decl]).2.2.1,globalStructContext) := by
    simp [globalStructContext,globalStructStart,globalStructDecl,decl,compileDecsExactHOL,compileDecsGlobalAddressExact_eq]
  have out := globalInitializedEntry_return template [decl] post _ _ _ globalStructContext entries (ofString "entry") body
    globalStructCrepContext shape 4 final 1 (by rfl) globalStructTarget_layout.2.2.2.1 globalStructTarget_aligned (by decide)
    (by intro d hd; simp at hd; subst d; rfl) (by exact declEval)
    (by simpa [beforeGlobalsContext,globalStructStart,decl,decShapesHOL,sizeOfShapeHOL,sizeOfShapesHOL,cakeBytesInWord,panBytesInWord] using compiled)
    (by simpa [decl,decShapesHOL,sizeOfShapeHOL,sizeOfShapesHOL,cakeBytesInWord,panBytesInWord] using allocated)
    (by decide) (by rfl) table sourceRun sourceBound
  obtain ⟨targetFinal,targetRun,_,_⟩ := out
  exact ⟨targetFinal,targetRun⟩
end SteppedFlapjack.Concrete
