import SteppedFlapjack.Concrete.Phase7NativeFacts
import SteppedFlapjack.Concrete.FixtureTargetLab
import SteppedFlapjack.StackToLabSteps.ExplicitSpan
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
  induction scalar <;> simp_all [expToHOL,compileExpExact,compileExpsExact,shapeToHOL,compileShapeExact]

theorem supported_structs_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (ctxt : ContextExact) :
    compileProgExact ctxt (progToHOL program) = progToHOL program := by
  induction supported generalizing ctxt <;> simp_all [progToHOL,shapeToHOL,compileProgExact,compileShapeExact]
  all_goals exact scalar_structs_fixed (by assumption) ctxt

/-- The executable allocation agrees with the original compiler. -/
theorem supportedAllocated_eq (program : Prog (RiscV.Word 64)) :
    supportedAllocated program = WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simp only [supportedAllocated,phase3WordConfig_eq,WordToWord.compileWith_eq_compile _ allocator]

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

/-- Call-aware scalar programs meet the compiler operation-arity check. -/
private theorem args_good {scope : List VarName} (args : List (Exp (RiscV.Word 64)))
    (scalar : ∀ e ∈ args, Scalar scope e) : everyExpListHOL panopArityTwoHOL (args.map expToHOL) = true := by
  induction args with
  | nil => simp [everyExpListHOL]
  | cons e es ih => simp [everyExpListHOL,scalar_goodPanops (scalar e (by simp)),ih (fun e he => scalar e (by simp [he]))]

theorem call_good {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : everyExpListHOL panopArityTwoHOL (expsOfHOL (progToHOL program)) = true := by
  induction supported with
  | base h => exact supported_goodPanops h
  | tail name args scalar => simpa [progToHOL,expsOfHOL] using args_good args scalar
  | call dest name args scalar cont ih => simp [progToHOL,expsOfHOL,everyExpList_append,args_good args scalar,ih]
  | decl name scalar body ih => simp [progToHOL,expsOfHOL,everyExpListHOL,scalar_goodPanops scalar,ih]
  | seq a b iha ihb => simp [progToHOL,expsOfHOL,everyExpList_append,iha,ihb]
  | ite scalar a b iha ihb => simp [progToHOL,expsOfHOL,everyExpListHOL,everyExpList_append,scalar_goodPanops scalar,iha,ihb]
  | «while» scalar body ih => simp [progToHOL,expsOfHOL,everyExpListHOL,scalar_goodPanops scalar,ih]


end SteppedFlapjack.Concrete
