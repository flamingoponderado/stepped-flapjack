import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.CrepToLoopSteps.RiscVInputs

/-! Shared source-to-Loop entry definitions. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- The compiler-selected Loop-to-Word context for a zero-argument entry. -/
def assignLoopEntryWordContext (entry : HolLoopProg 64) : Spt Nat :=
  makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL entry .ln) (LoopToWord.toNumSetHOL []))) .ln

end SteppedFlapjack.PanToCrepSteps
