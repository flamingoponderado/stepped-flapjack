import SteppedFlapjack.Concrete.GlobalDecodedSource
import SteppedFlapjack.Concrete.GlobalFrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.CrepToLoopSteps
theorem globalEntry_decodedLayout (post final : PanSemStateFiniteExact 64 Unit) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : panGlobalsStateRelHOLExact true globals (installSourceFunctions post entries) (installTargetFunctions final globals entries)) :
    GlobalLayout (globalEntryShapes post entries) globals := by
  intro name shape found
  unfold globalEntryShapes at found
  cases h : (globalEntrySource post entries).globals.lookup (ofString name) with
  | none => simp [h] at found
  | some value =>
    simp [h] at found
    subst shape
    rcases rel with ⟨_,_,_,_,_,_,_,_,globalRel,_,_,_,_,_,_,_,_,_,_⟩
    obtain ⟨addr,lookup,_,_,_,_⟩ := globalRel (ofString name) value h
    exact ⟨addr,lookup⟩

theorem globalEntry_decodedFfi (post final : PanSemStateFiniteExact 64 Unit) (globals : PanGlobalsContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (rel : panGlobalsStateRelHOLExact true globals (installSourceFunctions post entries) (installTargetFunctions final globals entries))
    (ffi : final.ffi = sourceFfi) : (globalEntrySource post entries).ffi = sourceFfi := by
  rcases rel with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,stateFfi,_,_,_,_,_⟩
  exact stateFfi.trans ffi
/-- Source functions have scalar parameters and supported, byte-ranged bodies. -/
def GlobalSupportedEntries (shapes : VarName → Option ShapeHOL)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ name params body ret, entries.lookup name = some (params,body,ret) →
      ∃ (scope : List VarName) (prog : Prog (RiscV.Word 64)),
        params = scope.map (fun n => (ofString n,ShapeHOL.one)) ∧ body = progToHOL prog ∧
        GlobalCallSupportedIn shapes scope prog ∧ ProgByteRanged prog

theorem target_table_from_supported (shapes : VarName → Option ShapeHOL)
    (globals : PanGlobalsContextExact 64) (layout : GlobalLayout shapes globals)
    (state : PanSemStateFiniteExact 64 Unit) (ctxt : PanToCrepContextExact 64)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (supportedEntries : GlobalSupportedEntries shapes entries) :
    CallFrontendCode ctxt (installTargetFunctions state globals entries).code := by
  intro name params body ret found
  change FLOOKUP (FUPDATE_LIST FEMPTY (entries.map (fun e => (e.1,e.2.1,compileProgExactHOL globals e.2.2.1,e.2.2.2))).reverse) name = _ at found
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,lookup_mapBodies] at found
  cases h : entries.lookup name with
  | none => simp [h] at found
  | some entry =>
    obtain ⟨ps,p,r⟩ := entry
    simp only [h,Option.map_some,Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    obtain ⟨scope,prog,rfl,rfl,supported,_⟩ := supportedEntries name ps p r h
    have shape := globalCallSupported_frontend layout supported _ (scalar_parameter_scope scope ctxt.funcs ctxt.eids)
    have result := globalCallFrontend_compiled shape
    convert result using 1; simp [ctxtFcExactHOL,mkCtxtExactHOL,panToCrepMakeVmapHOLExact,maxList_range,List.zip,List.map_map,Function.comp_def]
theorem supported_source_table (shapes : VarName → Option ShapeHOL)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (supportedEntries : GlobalSupportedEntries shapes entries) :
    ∀ name params body ret, entries.lookup name = some (params,body,ret) →
      ∃ scope, GlobalCallSupportedIn shapes scope (progOfHOL body) := by
  intro name params body ret found
  obtain ⟨scope,prog,_,rfl,supported,ranged⟩ := supportedEntries name params body ret found
  rw [progOfHOL_progToHOL prog ranged]
  exact ⟨scope,supported⟩
end SteppedFlapjack.Concrete
