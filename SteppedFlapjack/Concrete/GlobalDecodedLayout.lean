import SteppedFlapjack.Concrete.GlobalDecodedSource
import SteppedFlapjack.Concrete.GlobalFrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps
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
end SteppedFlapjack.Concrete
