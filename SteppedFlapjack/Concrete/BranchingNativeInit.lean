import SteppedFlapjack.Concrete.ComparisonWordSpan
import SteppedFlapjack.Concrete.BranchingWordSpan
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.Concrete.InitEStack
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

/-- The comparison compiler emits one bitmap word. -/
theorem comparison_nativeBitmaps :
 (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2).1 = [4] := by
  unfold comparisonWordPrograms comparisonCrepCode
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody branching_scalar]
  exact twoWordTables_native_bitmaps riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody
    (Ne.symm (entryName_fresh branchingHOL)) branching_scalar countdownRiscVBackend.wordToWordConf riscvConfig

/-- The branching-loop compiler emits one bitmap word. -/
theorem branchingLoop_nativeBitmaps :
 (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2).1 = [4] := by
  unfold branchWordPrograms branchCrepCode
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody branchingLoop_scalar]
  exact twoWordTables_native_bitmaps riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody
    (Ne.symm (entryName_fresh (progToHOL branchingLoop))) branchingLoop_scalar countdownRiscVBackend.wordToWordConf riscvConfig

/-- Actual initialized Stack state for the compiled comparison witness. -/
noncomputable def comparisonFixtureStack (cfg : LabToTarget.Config) := fixtureStack
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2).2.2.2 cfg

/-- Actual initialized Stack state for the compiled branching-loop witness. -/
noncomputable def branchingLoopFixtureStack (cfg : LabToTarget.Config) := fixtureStack
  (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2).2.2.2 cfg

/-- The original compiler supplies the comparison initializer validity. -/
theorem comparisonFixture_initOk (cfg : LabToTarget.Config) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (comparisonFixtureStack cfg) (fixtureWordOracle cfg) := by
  apply fixtureStack_nativeInitOk
  exact singleEntry_nativeGoodCode (progToHOL branching) comparisonWordPrograms comparison_panToWord

/-- The original compiler supplies the branching-loop initializer validity. -/
theorem branchingLoopFixture_initOk (cfg : LabToTarget.Config) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (branchingLoopFixtureStack cfg) (fixtureWordOracle cfg) := by
  apply fixtureStack_nativeInitOk
  exact singleEntry_nativeGoodCode (progToHOL branchingLoop) branchWordPrograms branchingLoop_panToWord

end SteppedFlapjack.Concrete
