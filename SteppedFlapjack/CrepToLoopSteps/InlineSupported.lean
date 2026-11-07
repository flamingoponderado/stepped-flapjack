import SteppedFlapjack.CrepToLoopSteps.InlineEntry
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact

/-! Inliner fixed points for the supported whole-program fragment. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.CrepInlineCanonical Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Every supported body is unchanged when its direct tail callee is absent
from the inline map. Branch and loop bodies need no restriction on the map. -/
theorem supportedCodeBody_inline_fixed {width : Nat} [NeZero width]
    (inl : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (keys : List CrepInlineMapHOLName) (support : ∀ k, inl.lookup k ≠ none → k ∈ keys)
    {p : CrepProgHOL width} (shape : SupportedCodeBody p)
    (noTail : ∀ init name, p = .seq init (.call none name []) → inl.lookup name = none) :
    inlineProgHOLCoreExact inl keys support p = p := by
  cases shape with
  | branch h => exact branchProgram_inline_fixed inl keys support h
  | tail h name => exact inline_tailEntry_fixed inl keys support _ h name [] (noTail _ name rfl)
  | loop hi _ hb ht => exact branchConditionWhileBranch_inline_fixed inl keys support _ hi _ _ _ hb ht
  | declWhile _ _ hb ht =>
    simp [inlineProgHOLCoreExact,branchProgram_inline_fixed inl keys support hb,
      branchProgram_inline_fixed inl keys support ht]
  | declLoop _ hi _ hb ht =>
    simp [inlineProgHOLCoreExact,branchConditionWhileBranch_inline_fixed inl keys support _ hi _ _ _ hb ht]

/-- The real top-level inliner preserves a supported program list when no
supported direct tail call targets a name selected for inlining. This
condition is stronger than necessary for self tail calls: the inliner removes
the current function from its inline map. -/
theorem compileInlTop_supported_fixed {width : Nat} [NeZero width]
    (names : List CrepInlineMapHOLName)
    (code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (shapes : ∀ name params p, (name,params,p) ∈ code → SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ code → callee ∉ names) :
    compileInlTopHOLExact names code = code := by
  unfold compileInlTopHOLExact compileInlProgHOLExactWithSupport
  conv_rhs => rw [← List.map_id code]
  apply List.map_congr_left
  intro entry member
  rcases entry with ⟨name,params,p⟩
  apply congrArg (fun q => (name,params,q))
  apply supportedCodeBody_inline_fixed _ _ _ (shapes name params p member)
  intro init callee eq
  subst p
  by_contra h
  have hmem := HolFiniteMapExact.erase_support _ _ (supportKeys_alistToFmapHOLExact _) name callee h
  simp only [List.mem_filter,List.mem_map] at hmem
  obtain ⟨⟨candidate,hcandidate,hkey⟩,_⟩ := hmem
  have hname : callee ∈ names := by
    have : candidate.1 ∈ names := List.contains_iff_mem.mp hcandidate.2
    simpa only [hkey] using this
  exact noTail name params init callee member hname

/-- The original Pancake-to-Crep code relation holds for the actual
post-inlining compiler output when its pre-inline bodies belong to the
supported fragment and its direct tail callees are not selected to inline. -/
theorem supported_compileProgDecls_codeRel {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width))
    (unique : ((compileProgDeclsHOLW declarations).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL declarations, localisedProgHOL entry.2.2.1 = true)
    (shapes : ∀ name params p, (name,params,p) ∈ compileToCrepExactHOLW declarations → SupportedCodeBody p)
    (noTail : ∀ name params init callee,
      (name,params,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW declarations →
        callee ∉ (functionsHOL (declarations.filter inlinableHOL)).map Prod.fst) :
    codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL declarations)) 0
        (getEidsFromDeclsHOL declarations))
      (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)
      (alistToFmapCodeExact (compileProgDeclsHOLW declarations)) := by
  have fixed := compileInlTop_supported_fixed
    ((functionsHOL (declarations.filter inlinableHOL)).map Prod.fst)
    (compileToCrepExactHOLW declarations) shapes noTail
  have sourceUnique : ((functionsHOL declarations).map Prod.fst).Nodup := by
    change ((compileInlTopHOLExact _ (compileToCrepExactHOLW declarations)).map Prod.fst).Nodup at unique
    rw [fixed] at unique
    simpa [compileToCrepExactHOLW, List.map_map, Function.comp_def] using unique
  change codeRelExactHOLW _ _
    (HolFiniteMapExact.empty.updateList (compileInlTopHOLExact _ _).reverse)
  rw [fixed]
  exact mkCtxtCodeImpCodeRelExactHOLW declarations sourceUnique localised

end SteppedFlapjack.CrepToLoopSteps
