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

/-- The actual native countdown output contains exactly its initial bitmap,
for every countdown constant and every Word compiler configuration. -/
theorem countdown_native_bitmap_exact (name : MlString) (initial returned : BitVec 64)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) :
    (countdownNativeRiscV name initial returned wc).1 = [4] := by
  apply countdown_native_single_bitmap
  apply supportedProgram_loopShapes
  exact countdown_crep_shapes name initial returned

set_option maxHeartbeats 1000000 in
/-- Successful compilation emits the exact singleton bitmap [4]. -/
theorem countdown_artifact_bitmap_exact (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (final : Flapjack.Compiler.Backend.Backend.Config)
    (hcompile : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend
      Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = some (bytes,bitmaps,final)) : bitmaps = [4] := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  let full := Flapjack.Pancake.Proofs.PanToTarget.compileProgMaxAsmExecutable countdownRiscVBackend
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig source
  have artifact : full.1 = some (bytes,bitmaps,final) := by
    simpa only [full,source,Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast_eq_fst] using hcompile
  have hfull : full = (some (bytes,bitmaps,final),full.2) := Prod.ext artifact rfl
  have hbm := (countdown_executableCompiler_lab name initial returned countdownMachineConfig rfl
    bytes bitmaps final full.2 (by simpa only [full,source] using hfull)).2
  exact hbm.symm.trans (countdown_native_bitmap_exact name initial returned _)

end SteppedFlapjack.PanToCrepSteps
