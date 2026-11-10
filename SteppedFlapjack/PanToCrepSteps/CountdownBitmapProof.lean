import SteppedFlapjack.PanToCrepSteps.CountdownCompilerShape
import SteppedFlapjack.PanToCrepSteps.DeclWhileSingleEntry
import SteppedFlapjack.CrepToLoopSteps.BitmapSourceShape

/-! Derive bitmap behavior from the concrete countdown source. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- The actual countdown Crep functions belong to the supported code fragment. -/
theorem countdown_crep_shapes (name : MlString) (initial returned : BitVec 64) :
    let body : ProgHOL 64 := .dec name .one (.const initial)
      (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))
    ∀ row ∈ compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram (ofString "main") body) (ofString "main")),
      SupportedCodeBody row.2.2 := by
  dsimp only
  simp only [compileProgDeclsHOLW,singleEntry_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil]
  intro row member
  rw [singleEntry_compileTop] at member
  simp only [compileToCrepExactHOLW,functionsHOL,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with first | second
  · subst row
    simp only [compFuncExactHOLW,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,Nat.zero_sub,
      compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact .tail (.expr (.leaf .skip)) _
  · subst row
    simp only [compFuncExactHOLW,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,Nat.zero_sub,
      declaredWhileAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL]
    apply scalarDeclWhile_supported
    · exact .const _
    · apply BranchCondition.scalar
      exact .local _ _ (scalarDeclContext_local _ _)
    · simp only [compileExpExactHOLList,compileExpExactHOL]
      exact .assign _ _ (scalarDeclContext_local _ _)
        (.op .sub (.local _ _ (scalarDeclContext_local _ _)) (.const _))
    · exact .return (.const _)

end SteppedFlapjack.PanToCrepSteps
