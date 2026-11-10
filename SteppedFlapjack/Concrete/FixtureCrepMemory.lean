import SteppedFlapjack.Concrete.InitEHeap
import SteppedFlapjack.Concrete.CountedApplications
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
namespace SteppedFlapjack.Concrete

/-- The initialized Stack heap agrees with any source fixture on its accessible domain. -/
theorem fixtureCrep_memory (program : Prog (RiscV.Word 64)) (fuel : Nat) (body : ProgHOL 64)
    (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    let source := panSimpSourceState program (clockedFixtureSource program fuel)
    crepToLoopMemRelHOLExact (crepStateFrom source body).memory (fixtureStack code cfg).memory
      (crepStateFrom source body).memaddrs := by
  dsimp only
  intro a member
  have h := fixtureStack_heapMemory code cfg good a
  change (WordLocW.word (initialWord a)) = (fixtureStack code cfg).memory a
  apply Eq.symm
  apply h
  simpa [crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
    panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate] using member
end SteppedFlapjack.Concrete
