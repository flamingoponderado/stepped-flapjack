import SteppedFlapjack.Concrete.NestedRow3
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def nestedColoredRow (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (colors : List (Nat × Nat)) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList colors)) (RowColoring.input row))

theorem nested_optimizedTable : nestedOptimizedWords =
  [(64,1,nestedColoredRow nestedRow0 nestedCols0),(65,1,nestedColoredRow nestedRow1 nestedCols1),
   (66,1,nestedColoredRow nestedRow2 nestedCols2),(67,1,nestedColoredRow nestedRow3 nestedCols3)] := by
  unfold nestedOptimizedWords nestedRawWords
  rw [nestedCall_loop_code]
  change [fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (nestedRow0,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (nestedRow1,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (nestedRow2,none),
    fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith RowColoring.limit 3 riscvConfig (nestedRow3,none)] = _
  rw [RowColoring.compiled_exact nestedRow0 nestedCols0 nestedGuard0 nestedFailure0 nestedExtract0,
    RowColoring.compiled_exact nestedRow1 nestedCols1 nestedGuard1 nestedFailure1 nestedExtract1,
    RowColoring.compiled_exact nestedRow2 nestedCols2 nestedGuard2 nestedFailure2 nestedExtract2,
    RowColoring.compiled_exact nestedRow3 nestedCols3 nestedGuard3 nestedFailure3 nestedExtract3]
  rfl


end SteppedFlapjack.Concrete
