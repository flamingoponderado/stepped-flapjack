import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
import SteppedFlapjack.PanToCrepSteps.CountdownNoFfi
import SteppedFlapjack.PanToCrepSteps.CountdownBitmapProof

/-! Connect the structural liveness evaluator to the actual countdown compiler. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps

/-- Countdown Lab program with the structural liveness evaluator and the
proved executable allocator. -/
noncomputable def countdownStructuralLabCode (name : MlString) (initial returned : BitVec 64) :=
  let body : ProgHOL 64 := .dec name .one (.const initial)
    (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
      (.return (.const returned)))
  let crep := compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram (ofString "main") body) (ofString "main"))
  let loops := compileProgWithStructuralLive riscvConfig.isa crep
  let words := loopToWordCompileHOL loops
  let allocated := (WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable
    countdownRiscVBackend.wordToWordConf riscvConfig words).2
  let stack := (WordToStack.Native.compileNative riscvConfig false allocated).2.2.2
  StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf
    (2 * DataToWord.maxHeapLimit 64 countdownRiscVBackend.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset stack

set_option maxHeartbeats 1000000 in
/-- The actual countdown Lab code is exactly the output of the structural
liveness and executable register-allocation pipeline. -/
theorem countdownStructuralLabCode_eq (name : MlString) (initial returned : BitVec 64) :
    countdownStructuralLabCode name initial returned =
      countdownStackLabCode name initial returned countdownRiscVBackend := by
  unfold countdownStructuralLabCode countdownStackLabCode countdownNativeRiscV
  rw [singleEntry_countdown_panToWord]
  rw [← compileProgWithStructuralLive_eq _ _ (countdown_crep_shapes name initial returned)]
  dsimp only
  rw [WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The original countdown frontend produces this exact entry wrapper for
all countdown constants and variable names. -/
theorem countdown_frontend_entry_exact (name : MlString) (initial returned : BitVec 64) :
    let body : ProgHOL 64 := .dec name .one (.const initial)
      (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))
    (compileProgHOLExact riscvConfig.isa
      (compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram (ofString "main") body) (ofString "main")))).head? =
    some (64,[],.mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))) := by
  dsimp only
  rw [← compileProgWithStructuralLive_eq _ _ (countdown_crep_shapes name initial returned)]
  simp only [compileProgDeclsHOLW,singleEntry_inline_selection_empty,
    CrepInlineRoute.compileInlTopHOLExact_nil]
  simp only [singleEntry_compileTop,singleEntry_main_freshName]
  with_unfolding_all rfl

end SteppedFlapjack.PanToCrepSteps
