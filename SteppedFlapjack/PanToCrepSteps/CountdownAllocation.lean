import SteppedFlapjack.PanToCrepSteps.CountdownWordLiteral
import Flapjack.Compiler.Backend.RegAlloc.Executable

/-! The zero-count allocation input used by the checked coloring. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc

/-- The loop row of the proved zero-count Word program. -/
def countdownZeroLoopRow : Nat × Nat × WordLangProgHOL (BitVec 64) :=
  (countdownWordLiteral 0 0).get ⟨1, by decide⟩

/-- The exact program passed to register allocation after the earlier Word
passes for the zero-count loop. -/
def countdownZeroAllocInput : WordLangProgHOL (BitVec 64) :=
  countdownPreAllocation countdownZeroLoopRow.2.1 countdownZeroLoopRow.2.2

/-- The loop row really comes from the original Pancake compiler. -/
theorem countdownZeroLoopRow_from_compiler :
    (panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64)))))))).drop 1 = [countdownZeroLoopRow] := by
  rw [countdownWordLiteral_zero_eq]
  rfl

end SteppedFlapjack.PanToCrepSteps
