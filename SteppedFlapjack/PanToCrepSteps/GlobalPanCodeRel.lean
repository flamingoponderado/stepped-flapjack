import SteppedFlapjack.CrepToLoopSteps.InlineSupported
import SteppedFlapjack.PanToCrepSteps.GlobalCodeRelations

/-! Source-to-Crep code relation for the actual global-lowered program. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps

/-- When the lowered source functions are localized and their compiled bodies
are fixed by the inliner, the source and actual post-inline Crep code tables
satisfy the frontend relation used by the global machine theorem. -/
theorem global_supported_panCrep_codeRel {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (pan : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (shapes : ∀ name params p, (name,params,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst) :
    codeRelExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start)))
        (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
      pan.code crep.code := by
  rw [panCode,crepCode]
  have emptyUpdate : (HolFiniteMapExact.empty.updateList [] : HolFiniteMapExact MlString (ShapeHOL × List Nat)) = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    rfl
  simpa [panToCrepMakeVmapHOLExact, sizeOfShapeHOL, sizeOfShapesHOL, emptyUpdate] using
    supported_compileProgDecls_codeRel (compileTopExactHOL declarations start) unique localised shapes noTail

/-- The same pre-inline syntax facts establish both the Pancake-to-Crep code
relation and the post-inline body shapes needed by the global machine bound. -/
theorem global_supported_panCrep_codeAndShapes {width : Nat} [NeZero width] {F : Type}
    (declarations : List (DeclHOL width)) (start : MlString)
    (pan : PanSemStateFiniteExact width F) (crep : CrepSemHOLState width F)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (shapes : ∀ name params p, (name,params,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst) :
    codeRelExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start)))
        (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
      pan.code crep.code ∧
    ∀ name params p, (name,params,p) ∈ compileProgDeclsHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p := by
  refine ⟨global_supported_panCrep_codeRel declarations start pan crep panCode crepCode unique localised shapes noTail,?_⟩
  intro name params p member
  have fixed := compileInlTop_supported_fixed
    ((functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (compileToCrepExactHOLW (compileTopExactHOL declarations start)) shapes noTail
  change (name,params,p) ∈ CrepInlineCanonical.compileInlTopHOLExact _ _ at member
  rw [fixed] at member
  exact shapes name params p member

end SteppedFlapjack.PanToCrepSteps
