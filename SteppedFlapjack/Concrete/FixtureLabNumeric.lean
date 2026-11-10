import SteppedFlapjack.Concrete.FixtureStackLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove
namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
private theorem fixtureUniformFactor : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel

set_option maxRecDepth 100000 in
private theorem fixtureInitCost : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^61) 24 : HolProg 64) = 361 := by decide +kernel

/-- A fixture with the checked code factor uses this numeric affine Lab clock. -/
theorem fixtureLabTick_numeric (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (n : Nat)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (coracle1 (fixtureStackOracle cfg)) = 1950) :
    fixtureLabTickLimit code cfg n = 111150*n + 1101 := by
  unfold fixtureLabTickLimit
  simp only [factor,fixtureUniformFactor,fixtureInitCost,flattenStepFactor]
  omega
end SteppedFlapjack.Concrete
