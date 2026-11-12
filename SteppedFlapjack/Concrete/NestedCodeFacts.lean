import SteppedFlapjack.Concrete.NestedOptTable
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem nested_bitmaps : nestedBitmaps = [4,2] := by
  unfold nestedBitmaps nestedNative
  rw [nested_optimizedTable]
  decide +kernel

theorem nested_frames : nestedFrameSizes = sptFromAList [(64,0),(65,2),(66,0),(67,0)] := by
  unfold nestedFrameSizes
  rw [nested_optimizedTable]
  decide +kernel

theorem nested_bitmapFits : 0xa0020018 + nestedBitmaps.length * 8 ≤ 0xa0410000 := by
  rw [nested_bitmaps]
  decide

theorem nested_entryFrame : nestedEntryFrame = 0 := by
  unfold nestedEntryFrame nestedEntry
  rw [nested_optimizedTable]
  decide +kernel

theorem nested_nativeSafe : fixtureStackSafe nestedCode = true := by
  unfold nestedCode nestedNative
  rw [nested_optimizedTable]
  decide +kernel

theorem nestedRow0_exact : nestedColoredRow nestedRow0 nestedCols0 =
    .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none) := by with_unfolding_all rfl
theorem nestedRow1_exact : nestedColoredRow nestedRow1 nestedCols1 =
    .seq (.move 1 [(44,0)])
      (.seq (.call (some ([2], ((Spt.ln.bn (((Spt.ln.bn (Spt.ls PUnit.unit)).bn Spt.ln).bn Spt.ln)).bn Spt.ln, Spt.ln),
        .move 1 [(4,2),(0,44)],65,2)) (some 66) []
        (some (2,.seq (.move 1 [(2,2),(0,44)]) (.raise 2),65,3)))
        (.seq .tick (.seq (.move 0 [(2,4)]) (.return 0 [2])))) := by with_unfolding_all rfl
theorem nestedRow2_exact : nestedColoredRow nestedRow2 nestedCols2 =
    .seq (.move 1 [(0,0)]) (.call none (some 67) [0] none) := by with_unfolding_all rfl
theorem nestedRow3_exact : nestedColoredRow nestedRow3 nestedCols3 =
    .seq (.move 1 [(0,0)]) (.seq (.inst (.const 2 (7 : BitVec 64)))
      (.seq (.move 0 [(2,2)]) (.return 0 [2]))) := by with_unfolding_all rfl


end SteppedFlapjack.Concrete
