import SteppedFlapjack.Concrete.FixtureTargetLab
import SteppedFlapjack.StackToLabSteps.ExplicitSpan
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove
namespace SteppedFlapjack.Concrete

/-- The fixture has no dynamic installations, so its Lab clock is linear in
the Stack visit bound with a static factor computed from its generated code. -/
noncomputable def fixtureLabTickLimit (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (n : Nat) : Nat :=
  let entry := (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
  let generated := sptFromAList (code1 countdownRiscVBackend.dataConf code)
  let factor := costFromFields riscvConfig.addrOffset 0 entry generated [4] (coracle1 (fixtureStackOracle cfg))
  flattenStepFactor * (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^61) 24 : HolProg 64) +
    factor * (uniformFactor (width := 64) countdownRiscVBackend.dataConf * n) + 4)

/-- The general oracle-prefix calculation specializes to that static factor. -/
theorem fixtureLabTickLimit_eq (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (n : Nat) :
    stackLabTickLimit countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset [4] code (fixtureStackOracle cfg) n =
      fixtureLabTickLimit code cfg n := by
  change stackLabTickLimit countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset [4] code
    (fun _ => (cfg,[],[])) n = _
  rw [stackLabTickLimit_emptyOracle]
  have oracle : coracle1 (fixtureStackOracle cfg) = (fun _ => (cfg,[],[])) := by funext i; rfl
  simp only [fixtureLabTickLimit,oracle,max_self]

/-- A successful fixture Stack entry reaches Lab at a clock computed from
its compiler inputs, preserving the FFI events. -/
theorem fixtureStack_lab_return (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (clock limit : Nat)
    (post : StackSemStateFiniteExact 64 LabToTarget.Config Unit)
    (run : StackSemEvaluate.evaluate (.call none (.inl 64) none,
      {(fixtureStack code cfg) with clock := clock}) = (some (.result (.loc 1 0)),post))
    (bound : StackSteps.steps (.call none (.inl 64) none,
      {(fixtureStack code cfg) with clock := clock}) ≤ limit) :
    ∃ labPost, LabSem.evaluate {(fixtureTargetLab code cfg ms) with clock :=
      (fixtureLabTickLimit code cfg limit)} =
      (.halt .success,labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  have entryEq : BvlToBvi.initGlobalsLocation = 64 := by decide
  rw [← fixtureLabTickLimit_eq]
  apply fullInitStackLab_explicit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf
    (2^61) 24 riscvConfig.addrOffset [4] code (fixtureTargetLab code cfg ms) fixtureSavedRegs 0 (fixtureStackOracle cfg)
    (by decide) (fixtureTargetLab_assumptions code cfg ms good) clock limit (some (.result (.loc 1 0))) post .success
  · simpa only [entryEq,fixtureTargetLab_stack] using run
  · simp
  · simpa only [entryEq,fixtureTargetLab_stack] using bound
  · simp [stackEntryClass]
end SteppedFlapjack.Concrete
