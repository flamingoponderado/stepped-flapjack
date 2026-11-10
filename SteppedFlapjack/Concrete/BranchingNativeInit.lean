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

/-- Actual initialized Stack state for the compiled comparison witness. -/
noncomputable def comparisonFixtureStack (cfg : LabToTarget.Config) := fixtureStack comparisonNativeCode cfg

/-- Actual initialized Stack state for the compiled branching-loop witness. -/
noncomputable def branchingLoopFixtureStack (cfg : LabToTarget.Config) := fixtureStack branchingLoopNativeCode cfg

/-- Word initialization for the comparison witness. -/
noncomputable def comparisonFixtureWord (cfg : LabToTarget.Config) := fixtureWord comparisonNativeCode
  (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2 cfg

/-- Word initialization for the branching-loop witness. -/
noncomputable def branchingLoopFixtureWord (cfg : LabToTarget.Config) := fixtureWord branchingLoopNativeCode
  (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 cfg

open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The comparison source reaches optimized Word code from the actual initializer. -/
theorem comparisonFixture_native_word (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let pan := panSimpSourceState branching (clockedFixtureSource branching 6)
    let crep := crepStateFrom pan branchingHOL
    let word := {(comparisonFixtureWord cfg) with clock := 6*comparisonLoopVisits+1}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) word
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep branchCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 7]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) word ≤ comparisonWordBound := by
  have memoryRel := fixtureCrep_memory branching 6 branchingHOL comparisonNativeCode cfg comparison_nativeGoodCode
  have h := branching_wholeWord (comparisonFixtureStack cfg).memory memoryRel context primitive handler (comparisonFixtureWord cfg) 0
  have frame := twoProgram_optimizedEntry_frame riscvConfig.isa (ofString "main") (entryName branchingHOL)
    branchCrepBody (Ne.symm (entryName_fresh branchingHOL)) branching_scalar comparisonNativeCode cfg
  have starter := fixtureStarter branching 6 comparisonLoopBudget branchingHOL comparisonCrepCode comparisonNativeCode
    (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2 cfg comparison_nativeGoodCode 0
    (6*comparisonLoopVisits+1) frame
  have codeEq : (comparisonFixtureWord cfg).code = sptFromAList
      (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2 := rfl
  rw [← codeEq] at h
  dsimp only [comparisonWordStarter,comparisonFixtureWord,comparisonFixtureStack] at h
  dsimp only at starter
  rw [starter] at h
  exact h

/-- The branching-loop source reaches optimized Word code from the actual initializer. -/
theorem branchingLoopFixture_native_word (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let pan := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
    let crep := crepStateFrom pan (progToHOL branchingLoop)
    let word := {(branchingLoopFixtureWord cfg) with clock := 6*branchLoopVisits+1}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) word
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 7]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) word ≤ branchWordBound := by
  have memoryRel := fixtureCrep_memory branchingLoop 23 (progToHOL branchingLoop) branchingLoopNativeCode cfg branchingLoop_nativeGoodCode
  have h := branchingLoop_wholeWord (branchingLoopFixtureStack cfg).memory memoryRel context primitive handler (branchingLoopFixtureWord cfg) 0
  have frame := twoProgram_optimizedEntry_frame riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop))
    branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop))) branchingLoop_scalar branchingLoopNativeCode cfg
  have starter := fixtureStarter branchingLoop 23 branchLoopBudget (progToHOL branchingLoop) branchCrepCode branchingLoopNativeCode
    (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 cfg branchingLoop_nativeGoodCode 0
    (6*branchLoopVisits+1) frame
  have codeEq : (branchingLoopFixtureWord cfg).code = sptFromAList
      (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2 := rfl
  rw [← codeEq] at h
  dsimp only [branchWordStarter,branchingLoopFixtureWord,branchingLoopFixtureStack] at h
  dsimp only at starter
  rw [starter] at h
  exact h

end SteppedFlapjack.Concrete
