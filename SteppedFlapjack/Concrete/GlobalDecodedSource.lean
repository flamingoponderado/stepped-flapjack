import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.PanToCrepSteps.GlobalInitialState
import Flapjack.Pancake.Semantics.PanSem.TotalEvalAgree
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
def globalEntrySource (post : PanSemStateFiniteExact 64 Unit)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : PanSemStateFiniteExact 64 Unit :=
  callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty
theorem globalEntrySource_support (post : PanSemStateFiniteExact 64 Unit)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    ∀ key, (globalEntrySource post entries).code.lookup key ≠ none → key ∈ entries.map Prod.fst := by
  intro key found
  change FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) key ≠ none at found
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at found
  cases h : entries.lookup key with
  | none => exact False.elim (found h)
  | some value =>
    obtain ⟨pre,post,eq,_⟩ := List.lookup_eq_some_iff.mp h
    rw [eq]
    simp
def globalEntryProduction (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : PanSemState (RiscV.Word 64) (FfiState Unit) := by
  letI : DecidablePred (globalEntrySource post entries).memaddrs := by change DecidablePred post.memaddrs; infer_instance
  letI : DecidablePred (globalEntrySource post entries).shMemaddrs := by change DecidablePred post.shMemaddrs; infer_instance
  exact panSemExecStateOfHOLWithKeys (globalEntrySource post entries) (sourceFfiState sourceFfi) (entries.map Prod.fst)
theorem globalEntryProduction_related (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (ffi : (globalEntrySource post entries).ffi = sourceFfi) :
    PanSemStateRelExec (globalEntryProduction post entries) (globalEntrySource post entries).toExact := by
  let _ : DecidablePred (globalEntrySource post entries).memaddrs := by change DecidablePred post.memaddrs; infer_instance
  let _ : DecidablePred (globalEntrySource post entries).shMemaddrs := by change DecidablePred post.shMemaddrs; infer_instance
  unfold globalEntryProduction
  apply panSemExecStateOfHOLWithKeys_rel
  · rw [ffi]; exact sourceFfiState_rel _
  · exact globalEntrySource_support post entries
theorem globalEntryProduction_ranged (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    PanSemStateRelExecRanged (globalEntryProduction post entries) := by
  let _ : DecidablePred (globalEntrySource post entries).memaddrs := by change DecidablePred post.memaddrs; infer_instance
  let _ : DecidablePred (globalEntrySource post entries).shMemaddrs := by change DecidablePred post.shMemaddrs; infer_instance
  unfold globalEntryProduction
  exact panSemExecStateOfHOLWithKeys_ranged _ _ _

private theorem entryRanged (entry : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :
    PanLangEntryByteRanged (panLangEntryOfHOL entry) := by
  obtain ⟨params,body,ret⟩ := entry
  refine ⟨?_,progOfHOL_byteRanged_bridge body,shapeOfHOL_byteRanged_bridge ret⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨nameRanged_toStringOfBytes_bridge q.1,shapeOfHOL_byteRanged_bridge q.2⟩
private theorem decodedCodeRanged (f : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (keys : List MlS) (name : String) (entry : List (VarName × Shape) × Prog (RiscV.Word 64) × Shape)
    (found : lookupInfo name (mlFunctionToInfoMap (fun k => (f k).map panLangEntryOfHOL) keys) = some entry) :
    PanLangEntryByteRanged entry := by
  induction keys with
  | nil => simp [mlFunctionToInfoMap,lookupInfo] at found
  | cons key rest ih =>
    cases h : f key with
    | none => simp only [mlFunctionToInfoMap,h,Option.map_none] at found; exact ih found
    | some value =>
      simp only [mlFunctionToInfoMap,h,Option.map_some,lookupInfo] at found
      split at found
      · cases found; exact entryRanged value
      · exact ih found

theorem globalEntryProduction_localsWord (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    WordLocals (globalEntryProduction post entries).locals := by
  intro name value found
  simp [globalEntryProduction,panSemExecStateOfHOLWithKeys,panSemStateOfExactWithKeys,globalEntrySource,
    callEntryStateHOLFinite,installSourceFunctions,HolFiniteMapExact.lookup_empty] at found
theorem globalEntryProduction_shapes (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (shapes : VarName → Option ShapeHOL)
    (shapeMap : ∀ name, NameRanged name → ((globalEntrySource post entries).globals.lookup (ofString name)).map shapeOfHOLExact = shapes name) :
    GlobalHOLShapes shapes (globalEntryProduction post entries).globals := by
  intro name rangedName
  have h := shapeMap name rangedName
  unfold globalEntryProduction panSemExecStateOfHOLWithKeys panSemStateOfExactWithKeys
  simp only [Option.map_map,Function.comp_def,panValueToHOL_panValueOfHOL]
  exact h

theorem globalEntryProduction_codeRanged (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    ∀ name entry, panSemCodeLookup (globalEntryProduction post entries).code name = some entry → PanLangEntryByteRanged entry := by
  intro name entry found
  apply decodedCodeRanged (fun k => (globalEntrySource post entries).code.lookup k) (entries.map Prod.fst) name entry
  exact found

private theorem mapMember {β : Type} (f : MlS → Option β) (keys : List MlS) (name : String) (value : β)
    (member : (name,value) ∈ mlFunctionToInfoMap f keys) :
    ∃ key ∈ keys, name = toStringOfBytes key ∧ f key = some value := by
  induction keys with
  | nil => simp [mlFunctionToInfoMap] at member
  | cons key tail ih =>
    cases h : f key with
    | none =>
      simp only [mlFunctionToInfoMap,h] at member
      obtain ⟨k,hk,hn,hv⟩ := ih member
      exact ⟨k,by simp [hk],hn,hv⟩
    | some v =>
      simp only [mlFunctionToInfoMap,h,List.mem_cons,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩ | member
      · exact ⟨key,by simp,rfl,h⟩
      · obtain ⟨k,hk,hn,hv⟩ := ih member
        exact ⟨k,by simp [hk],hn,hv⟩
theorem globalEntryProduction_codeShape (post : PanSemStateFiniteExact 64 Unit)
    [DecidablePred post.memaddrs] [DecidablePred post.shMemaddrs]
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (shapes : VarName → Option ShapeHOL)
    (table : ∀ name params body ret, entries.lookup name = some (params,body,ret) →
      ∃ scope, GlobalCallSupportedIn shapes scope (progOfHOL body)) :
    ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode (globalEntryProduction post entries).code →
      ∃ scope, GlobalCallSupportedIn shapes scope body := by
  intro name params body member
  simp only [countedFunctionsOfCode,List.mem_map] at member
  obtain ⟨row,hrow,eq⟩ := member
  obtain ⟨key,originalParams,originalBody,originalRet⟩ := row
  simp only [Prod.mk.injEq] at eq
  obtain ⟨rfl,rfl,rfl⟩ := eq
  have hrow : (key,(originalParams,originalBody,originalRet)) ∈
      mlFunctionToInfoMap (fun k => ((globalEntrySource post entries).code.lookup k).map panLangEntryOfHOL) (entries.map Prod.fst) := hrow
  obtain ⟨k,_,_,found⟩ := mapMember _ _ _ _ hrow
  simp only [Option.map_eq_some_iff] at found
  obtain ⟨⟨params,body,ret⟩,hlookup,heq⟩ := found
  change FLOOKUP (FUPDATE_LIST FEMPTY entries.reverse) k = _ at hlookup
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at hlookup
  obtain ⟨scope,supported⟩ := table k params body ret hlookup
  cases heq
  exact ⟨scope,supported⟩
/-- Shapes read from the initialized source globals. -/
def globalEntryShapes (post : PanSemStateFiniteExact 64 Unit)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (name : VarName) : Option ShapeHOL :=
  ((globalEntrySource post entries).globals.lookup (ofString name)).map shapeOfHOLExact

end SteppedFlapjack.Concrete
