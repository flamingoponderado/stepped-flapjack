import SteppedFlapjack.Concrete.Phase7Affine
import SteppedFlapjack.PanToCrepSteps.SingleEntryNativeGoodCode
import SteppedFlapjack.Concrete.SimpRun

/-! Connect supported programs to the actual Pancake compiler. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Pancake.PanStructs.CompileShapeExact

theorem scalar_structs_fixed {scope : List VarName} {e : Exp (RiscV.Word 64)}
    (scalar : Scalar scope e) (ctxt : ContextExact) : compileExpExact ctxt (expToHOL e) = expToHOL e := by
  induction scalar <;> simp_all [expToHOL,compileExpExact,compileExpsExact]

theorem supported_structs_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (ctxt : ContextExact) :
    compileProgExact ctxt (progToHOL program) = progToHOL program := by
  induction supported generalizing ctxt <;> simp_all [progToHOL,shapeToHOL,compileProgExact,compileShapeExact]
  all_goals exact scalar_structs_fixed (by assumption) ctxt

/-- Struct lowering leaves every supported singleton program unchanged. -/
theorem supported_structs_declarations (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    compileTopExact (declarations (progToHOL program)) = declarations (progToHOL program) := by
  simp [declarations,singleEntryProgram,compileTopExact,getNamesExact,compileDeclsExact,compileShapeExact,
    supported_structs_fixed supported.1]

/-- The original Pancake compiler selects exactly the generated Word program. -/
theorem supported_panToWord (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    panToWordCompileProgHOL riscvConfig.isa (declarations (progToHOL program)) = supportedWordPrograms program := by
  unfold panToWordCompileProgHOL
  rw [supported_panSimp_declarations program supported]
  dsimp only
  rw [supported_structs_declarations (panSimpProg program) (supported_panSimp program supported).1]
  rfl
/-- The executable allocation agrees with the original compiler. -/
theorem supportedAllocated_eq (program : Prog (RiscV.Word 64)) :
    supportedAllocated program = WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simp only [supportedAllocated,phase3WordConfig_eq,WordToWord.compileWith_eq_compile _ allocator]

set_option maxHeartbeats 1000000 in
/-- Native Stack code satisfies the original compiler's good-code contract. -/
theorem supported_nativeGoodCode (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    StackToLab.Proofs.GoodCode.goodCode 24 (supportedNative program).2.2.2 := by
  unfold supportedNative
  rw [supportedAllocated_eq]
  exact singleEntry_nativeGoodCode (progToHOL program) (supportedWordPrograms program) (supported_panToWord program supported)

private theorem scalar_goodPanops {scope : List VarName} {e : Exp (RiscV.Word 64)} (scalar : Scalar scope e) :
    everyExpHOL panopArityTwoHOL (expToHOL e) = true := by
  induction scalar <;> simp_all [expToHOL,everyExpHOL,everyExpListHOL,panopArityTwoHOL]

private theorem everyExpList_append (a b : List (ExpHOL 64)) :
    everyExpListHOL panopArityTwoHOL (a ++ b) =
      (everyExpListHOL panopArityTwoHOL a && everyExpListHOL panopArityTwoHOL b) := by
  induction a <;> simp_all [everyExpListHOL,Bool.and_assoc]

private theorem supported_goodPanops {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : everyExpListHOL panopArityTwoHOL (expsOfHOL (progToHOL program)) = true := by
  induction supported <;> simp_all [progToHOL,expsOfHOL,everyExpListHOL,everyExpList_append]
  all_goals exact scalar_goodPanops (by assumption)

/-- Supported source programs meet the compiler's source good-code check. -/
theorem supported_pancakeGoodCode (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    pancakeGoodCodeHOL (declarations (progToHOL program)) = true := by
  simpa [pancakeGoodCodeHOL,declarations,singleEntryProgram,goodPanopsHOL] using supported_goodPanops supported.1

/-- The actual filtered Lab program meets the machine's good-code guard. -/
theorem supported_labGoodCode (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab (supportedNative program).2.2.2
        (fixtureCompilerConfig (supportedNative program).2.2.2)).code) := by
  have h := singleEntry_labGoodCode (progToHOL program) (supportedWordPrograms program)
    (supported_panToWord program supported) (supported_pancakeGoodCode program supported)
  simpa only [supportedNative,supportedAllocated_eq,fixtureLab] using h

/-- The full compiler emits precisely the bytes loaded into the fixture. -/
theorem supported_compiler_output (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
    (safe : fixtureStackSafe (supportedNative program).2.2.2 = true)
    (success : (fixtureRemoveLabels (supportedNative program).2.2.2).isSome = true) :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL program)) = some (fixtureCodeBytes (supportedNative program).2.2.2,[4],final) := by
  apply fixturePancakeCompiler_output (progToHOL program) (supportedWordPrograms program) (supportedNative program).2.2.2
    (supported_panToWord program supported) ?_ ?_ safe success
  · simp only [supportedNative,supportedAllocated_eq]
  · simpa only [supportedNative,supportedAllocated_eq] using supported_native_bitmap program supported
end SteppedFlapjack.Concrete
