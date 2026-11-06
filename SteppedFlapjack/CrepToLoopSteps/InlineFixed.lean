import SteppedFlapjack.CrepToLoopSteps.SimpFixed
import Flapjack.Pancake.PanToCrep.CompileExact

/-! The actual Crep inliner preserves the supported call-free fragment. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.CrepInlineCanonical Flapjack.Pancake.PanLang

variable {width : Nat} [NeZero width]
variable (inl : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
variable (keys : List CrepInlineMapHOLName)
variable (support : ∀ key, inl.lookup key ≠ none → key ∈ keys)

theorem exprProgram_inline_fixed {p : CrepProgHOL width} (shape : ExprProgram p) :
    inlineProgHOLCoreExact inl keys support p = p := by
  induction shape with
  | leaf h => cases h <;> simp [inlineProgHOLCoreExact]
  | returnNil => simp [inlineProgHOLCoreExact]
  | returnOne h => simp [inlineProgHOLCoreExact]
  | assign name h => simp [inlineProgHOLCoreExact]
  | storeGlob name h => simp [inlineProgHOLCoreExact]
  | store hd hs => simp [inlineProgHOLCoreExact]
  | seq ha hb iha ihb => simp [inlineProgHOLCoreExact,iha,ihb]

theorem branchProgram_inline_fixed {p : CrepProgHOL width} (shape : BranchProgram p) :
    inlineProgHOLCoreExact inl keys support p = p := by
  induction shape with
  | expr h => exact exprProgram_inline_fixed inl keys support h
  | dec he hb ih => simp [inlineProgHOLCoreExact,ih]
  | seq ha hb iha ihb => simp [inlineProgHOLCoreExact,iha,ihb]
  | ite hc ha hb iha ihb => simp [inlineProgHOLCoreExact,iha,ihb]

/-- Inlining leaves the supported initialization, loop, and tail unchanged for
any inline map, including maps containing recursive or duplicate names. -/
theorem branchConditionWhileBranch_inline_fixed
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail) :
    inlineProgHOLCoreExact inl keys support (.seq init (.seq (.while condition body) tail)) =
      .seq init (.seq (.while condition body) tail) := by
  simp [inlineProgHOLCoreExact,branchProgram_inline_fixed inl keys support initShape,
    branchProgram_inline_fixed inl keys support bodyShape,branchProgram_inline_fixed inl keys support tailShape]

/-- A supported entry of the pre-inlining Crep list is retained at the same
index by whole-program Pancake-to-Crep compilation. -/
theorem compileProgDecls_supported_entry
    (declarations : List (Pancake.PanLang.DeclHOL width))
    (index : Nat) (hi : index < (compileToCrepExactHOLW declarations).length)
    (name : Basis.Pure.MlString.MlString)
    (init : CrepProgHOL width) (initShape : BranchProgram init)
    (condition : CrepExpHOL width)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (entry : (compileToCrepExactHOLW declarations)[index] =
      (name,[],.seq init (.seq (.while condition body) tail))) :
    ∃ h : index < (compileProgDeclsHOLW declarations).length,
      (compileProgDeclsHOLW declarations)[index]'h = (name,[],.seq init (.seq (.while condition body) tail)) := by
  unfold compileProgDeclsHOLW compileInlTopHOLExact compileInlProgHOLExactWithSupport
  refine ⟨by simpa using hi,?_⟩
  simp only [List.getElem_map,entry]
  rw [branchConditionWhileBranch_inline_fixed _ _ _ init initShape condition body tail bodyShape tailShape]

/-- For a zero-parameter Pancake function at a given function-list index,
whole-program compilation produces its exact supported Crep body at that
same index, including the real inlining pass. -/
theorem compileProgDecls_pancake_entry
    (declarations : List (DeclHOL width)) (index : Nat)
    (hi : index < (functionsHOL declarations).length) (name : Basis.Pure.MlString.MlString)
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width) (returnShape : ShapeHOL)
    (entry : (functionsHOL declarations)[index] =
      (name,[],.seq init (.seq (.while condition body) tail),returnShape))
    (ctxt : PanToCrepContextExact width)
    (ctxtDef : ctxt = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL declarations)) (sizeOfShapeHOL (.comb []) - 1)
      (getEidsFromDeclsHOL declarations))
    (initShape : BranchProgram (compileProgExactHOLW ctxt init))
    (conditionCrep : CrepExpHOL width)
    (conditionDef : compileExpExactHOLW ctxt condition = ([conditionCrep],.one))
    (bodyShape : BranchProgram (compileProgExactHOLW ctxt body))
    (tailShape : BranchProgram (compileProgExactHOLW ctxt tail)) :
    ∃ h : index < (compileProgDeclsHOLW declarations).length,
      (compileProgDeclsHOLW declarations)[index]'h =
        (name,[],compileProgExactHOLW ctxt (.seq init (.seq (.while condition body) tail))) := by
  have pWhile : compileProgExactHOLW ctxt (.seq init (.seq (.while condition body) tail)) =
      .seq (compileProgExactHOLW ctxt init)
        (.seq (.while conditionCrep (compileProgExactHOLW ctxt body)) (compileProgExactHOLW ctxt tail)) := by
    simp [compileProgExactHOLW,compileWhileExactHOLW,conditionDef]
  have hpre : index < (compileToCrepExactHOLW declarations).length := by
    simpa [compileToCrepExactHOLW] using hi
  have epre : (compileToCrepExactHOLW declarations)[index] =
      (name,[],.seq (compileProgExactHOLW ctxt init)
        (.seq (.while conditionCrep (compileProgExactHOLW ctxt body)) (compileProgExactHOLW ctxt tail))) := by
    simp only [compileToCrepExactHOLW,List.getElem_map,entry]
    have ctxtDef' := ctxtDef
    simp only [sizeOfShapeHOL,sizeOfShapesHOL,Nat.zero_sub] at ctxtDef'
    simp only [crepVarsHOL,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,List.range_zero,
      compFuncExactHOLW,Nat.zero_sub]
    rw [← ctxtDef',pWhile]
  obtain ⟨bound,found⟩ := compileProgDecls_supported_entry declarations index hpre name
    _ initShape conditionCrep _ _ bodyShape tailShape epre
  exact ⟨bound,by simpa only [pWhile] using found⟩

end SteppedFlapjack.CrepToLoopSteps
