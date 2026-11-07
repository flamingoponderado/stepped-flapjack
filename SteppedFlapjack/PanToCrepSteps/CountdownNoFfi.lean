import SteppedFlapjack.PanToCrepSteps.CountdownNoShare
import SteppedFlapjack.WordToStackSteps.FfiFree

/-! Exclude external calls from the actual countdown compiler output. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

set_option maxHeartbeats 1000000 in
/-- The actual compiled countdown Lab code has no external-call names. -/
theorem countdown_lab_noFfi (name : MlString) (initial returned : BitVec 64) :
    findFfiNames (countdownStackLabCode name initial returned countdownRiscVBackend) = [] := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  let word := panToWordCompileProgHOL riscvConfig.isa source
  let allocated := (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig word).2
  have wordShapes : ∀ row ∈ word, SteppedFlapjack.LoopLiveSteps.WordTailEntryShape row.2.2 ∨ LoopSequence row.2.2 := by
    dsimp only [word,source]
    rw [singleEntry_countdown_panToWord]
    apply SteppedFlapjack.LoopToWordSteps.loopProgram_bitmapShapes
    apply SteppedFlapjack.CrepToLoopSteps.supportedProgram_loopShapes
    exact countdown_crep_shapes name initial returned
  have shapes := wholeCompile_tailOrLoop_exactShape countdownRiscVBackend.wordToWordConf riscvConfig word wordShapes
  have safe := compileNative_noFfi riscvConfig allocated shapes
  apply SteppedFlapjack.LabToTargetSteps.stackToLab_noFfi
  exact safe

set_option maxHeartbeats 1000000 in
/-- Successful compilation of a countdown has the empty FFI interface. -/
theorem countdown_artifact_emptyFfi (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (final : Backend.Config)
    (hcompile : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = some (bytes,bitmaps,final)) : final.labConf.ffiNames = some [] := by
  have h := (countdown_artifact_noSharedMetadata name initial returned bytes bitmaps final hcompile).2
  simpa only [countdown_lab_noFfi] using h

end SteppedFlapjack.PanToCrepSteps
