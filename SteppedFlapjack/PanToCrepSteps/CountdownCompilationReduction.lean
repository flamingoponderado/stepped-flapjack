import SteppedFlapjack.PanToCrepSteps.CountdownNoFfi
import SteppedFlapjack.PanToCrepSteps.CountdownBitmapProof

/-! Exact reduction of the callable countdown compiler to its Lab pass. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

set_option maxHeartbeats 1000000 in
/-- The full artifact compiler is exactly the Lab compiler with the proved
singleton bitmap attached. This equation includes failure as well as success. -/
theorem countdown_artifact_eq_lab (name : MlString) (initial returned : BitVec 64) :
    compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) =
    Backend.attachBitmaps .ln countdownRiscVBackend ([4] : List (BitVec 64))
      (LabToTarget.compile riscvConfig countdownRiscVBackend.labConf
        (countdownStackLabCode name initial returned countdownRiscVBackend)) := by
  rw [compileProgAsmFast_eq_fst]
  simp only [compileProgMaxAsmExecutable, WordToWord.compileExecutable_eq]
  change Backend.fromStack riscvConfig countdownRiscVBackend .ln
    (countdownNativeRiscV name initial returned countdownRiscVBackend.wordToWordConf).2.2.2
    (countdownNativeRiscV name initial returned countdownRiscVBackend.wordToWordConf).1 = _
  rw [countdown_native_bitmap_exact]
  rfl

set_option maxHeartbeats 1000000 in
/-- Compilation succeeds exactly when the final label-removal pass succeeds.
All earlier compiler passes, bitmap construction and FFI selection are accounted
for by the actual countdown compiler. -/
theorem countdown_artifact_success_iff_removeLabels (name : MlString) (initial returned : BitVec 64) :
    (compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned))))))).isSome =
    (LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (countdownStackLabCode name initial returned countdownRiscVBackend))).isSome := by
  have hnames : LabToTarget.findFfiNames
      (LabFilter.filterSkip (countdownStackLabCode name initial returned countdownRiscVBackend)) = [] := by
    rw [LabToTarget.FilterSkip.findFfiNamesFilterSkip, countdown_lab_noFfi]
  have hffi : countdownRiscVBackend.labConf.ffiNames = none := rfl
  have hclock : countdownRiscVBackend.labConf.initClock = 5 := rfl
  have hpos : countdownRiscVBackend.labConf.pos = 0 := rfl
  have hlabels : countdownRiscVBackend.labConf.labels = .ln := rfl
  rw [countdown_artifact_eq_lab]
  simp only [LabToTarget.compile, LabToTarget.compileLab, hnames, hffi, hclock, hpos, hlabels]
  cases h : LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (countdownStackLabCode name initial returned countdownRiscVBackend)) with
  | none => simp [Backend.attachBitmaps]
  | some result => cases result; simp [Backend.attachBitmaps]

end SteppedFlapjack.PanToCrepSteps
