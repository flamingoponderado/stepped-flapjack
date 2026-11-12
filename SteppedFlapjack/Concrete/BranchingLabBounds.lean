import SteppedFlapjack.Concrete.FixtureLabNumeric
import SteppedFlapjack.Concrete.BranchingFrames
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove
namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem branchFactor (cfg : LabToTarget.Config) :
 costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
 (sptFromAList (code1 countdownRiscVBackend.dataConf branchingLoopNativeCode)) [4] (coracle1 (fixtureStackOracle cfg)) = 1950 := by
 simp only [costFromFields, oracleBitmapBudget, Nat.add_zero, List.range_zero, List.flatMap_nil, maxListNat]
 unfold branchingLoopNativeCode
 rw [branch_optimized_table]
 decide +kernel

/-- Numeric Lab clock for the branching-loop witness. -/
theorem branchingLoopLabTick_closed (cfg : LabToTarget.Config) :
    fixtureLabTickLimit branchingLoopNativeCode cfg 348971665463 = 38788200616213551 := by
  rw [fixtureLabTick_numeric _ _ _ (branchFactor cfg)]

end SteppedFlapjack.Concrete
