import SteppedFlapjack.Concrete.ComparisonWordSpan
import SteppedFlapjack.Concrete.BranchingWordSpan
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.Concrete.TwoProgramNativeEntry
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
namespace SteppedFlapjack.Concrete

private theorem comparison_structs : Pancake.PanStructs.CompileShapeExact.compileTopExact (declarations branchingHOL) = declarations branchingHOL := by
  simp [declarations,singleEntryProgram,Pancake.PanStructs.CompileShapeExact.compileTopExact,
    Pancake.PanStructs.CompileShapeExact.getNamesExact,Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Pancake.PanStructs.CompileShapeExact.compileProgExact,Pancake.PanStructs.CompileShapeExact.compileExpExact,
    Pancake.PanStructs.CompileShapeExact.compileShapeExact,branchingHOL]

/-- The comparison witness uses its actual original-compiler Word table. -/
theorem comparison_panToWord : panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL branching)) = comparisonWordPrograms := by
  rw [← branching_hol_eq]
  change panToWordCompileProgHOL riscvConfig.isa (declarations branchingHOL) = _
  unfold panToWordCompileProgHOL
  rw [branching_simp_declarations]
  dsimp only
  rw [comparison_structs]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms branchingHOL)) = _
  rw [branching_crep_code]
  rfl

private theorem branchingLoop_structs : Pancake.PanStructs.CompileShapeExact.compileTopExact (declarations (progToHOL branchingLoop)) = declarations (progToHOL branchingLoop) := by
  simp [declarations,singleEntryProgram,Pancake.PanStructs.CompileShapeExact.compileTopExact,
    Pancake.PanStructs.CompileShapeExact.getNamesExact,Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Pancake.PanStructs.CompileShapeExact.compileProgExact,Pancake.PanStructs.CompileShapeExact.compileExpExact,
    Pancake.PanStructs.CompileShapeExact.compileShapeExact,
    branchingLoop,progToHOL,expToHOL,shapeToHOL]

/-- The branching-loop witness uses its actual original-compiler Word table. -/
theorem branchingLoop_panToWord : panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL branchingLoop)) = branchWordPrograms := by
  change panToWordCompileProgHOL riscvConfig.isa (declarations (progToHOL branchingLoop)) = _
  unfold panToWordCompileProgHOL
  rw [branchingLoop_simp_declarations]
  dsimp only
  rw [branchingLoop_structs]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (progToHOL branchingLoop))) = _
  rw [branchingLoop_crep_code]
  rfl

/-- Native Stack code emitted for the comparison witness. -/
noncomputable def comparisonNativeCode :=
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2).2.2.2

/-- Native Stack code emitted for the branching-loop witness. -/
noncomputable def branchingLoopNativeCode :=
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2).2.2.2

/-- The original compiler establishes good comparison code. -/
theorem comparison_nativeGoodCode : StackToLab.Proofs.GoodCode.goodCode 24 comparisonNativeCode :=
  singleEntry_nativeGoodCode (progToHOL branching) comparisonWordPrograms comparison_panToWord

/-- The original compiler establishes good branching-loop code. -/
theorem branchingLoop_nativeGoodCode : StackToLab.Proofs.GoodCode.goodCode 24 branchingLoopNativeCode :=
  singleEntry_nativeGoodCode (progToHOL branchingLoop) branchWordPrograms branchingLoop_panToWord

/-- Word initialization for the branching-loop witness. -/
noncomputable def branchingLoopFixtureWord (cfg : LabToTarget.Config) := fixtureWord branchingLoopNativeCode
  (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 cfg

open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

end SteppedFlapjack.Concrete
