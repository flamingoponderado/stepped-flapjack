import SteppedFlapjack.Concrete.InitEStack
import SteppedFlapjack.Concrete.FixtureByteDomain
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.Semantics.TargetProps.CalleeSaved
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.Semantics.TargetProps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.Concrete

/-- Assembly inputs for the aligned init-e-shaped Lab layout. `makeInit` reads
only the integer and floating-point registers; the other fields are placeholders
until the concrete machine initialization in Phase 6. -/
def fixtureAsm : AsmState 64 := {
 regs := fun r => if r = 11 then heapBase else if r = 12 then BitVec.ofNat 64 heapEnd else if r = 13 then BitVec.ofNat 64 ramEnd else 0
 fpRegs := fun _ => 0
 mem := fun _ => 0
 memDomain := fun _ => False
 pc := 4096
 lr := 1
 align := 4
 be := false
 failed := false }
/-- The Lab fixture produced by the original target initializer. -/
noncomputable def fixtureTargetLab (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state) :=
 LabToTarget.makeInit (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi fixtureAsm (fixtureLabMemoryFor code) (fun a => decide (fixtureLabDomain a))
  (fun a => decide (sharedAddress a)) ms (fixtureLab code cfg).code (LabToTarget.compile riscvConfig)
  0x800f0134 0xecc
  (fixtureLab code cfg).compileOracle

/-- Machine-side Lab initialization for the actual compiler bitmap list. -/
noncomputable def configuredTargetLab (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (ms : RiscV.L3.riscv_state) :=
  LabToTarget.makeInit (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi fixtureAsm
    (configuredLabMemory code bs) (fun a => decide (configuredLabDomain bs a))
    (fun a => decide (sharedAddress a)) ms (configuredLab code cfg bs).code (LabToTarget.compile riscvConfig)
    0x800f0134 0xecc (configuredLab code cfg bs).compileOracle

theorem configuredTargetLab_shape (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (ms : RiscV.L3.riscv_state) :
    configuredTargetLab code cfg bs ms = {(configuredLab code cfg bs) with
      ioRegs := targetIoRegs (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms,
      ioFpRegs := targetIoFpRegs (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms,
      ccRegs := targetCcRegs (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms,
      ccFpRegs := targetCcFpRegs (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms} := by
  unfold configuredTargetLab LabToTarget.makeInit configuredLab fixtureLab
  congr 1
  all_goals try (with_unfolding_all rfl)
  funext r
  simp only [fixtureAsm,fixtureLabRegs]
  repeat' first | split | simp_all

theorem configuredTargetLab_one (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (ms : RiscV.L3.riscv_state) : configuredTargetLab code cfg [4] ms = fixtureTargetLab code cfg ms := by
  have labEq := configuredLab_one code cfg
  have memEq := congrArg (fun lab => lab.memory) labEq
  have domEq := congrArg (fun lab => lab.memDomain) labEq
  change configuredLabMemory code [4] = fixtureLabMemoryFor code at memEq
  change (fun a => decide (configuredLabDomain [4] a)) =
    (fun a => decide (fixtureLabDomain a)) at domEq
  unfold configuredTargetLab fixtureTargetLab
  rw [memEq, domEq, configuredLab_one]

open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

theorem configuredTargetLab_stack (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (ms : RiscV.L3.riscv_state) :
    (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
      bs code (configuredTargetLab code cfg bs ms) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1 = configuredStack code cfg bs := by
  rw [configuredTargetLab_shape]
  unfold configuredStack
  rw [fullMakeInit_eq,fullMakeInit_eq]
  rfl

theorem fixtureTargetLab_stack (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state) :
 (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
  [4] code (fixtureTargetLab code cfg ms) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1 = fixtureStack code cfg := by
 have h := configuredTargetLab_stack code cfg [4] ms
 rw [configuredTargetLab_one, configuredStack_one] at h
 exact h

private theorem fixtureSavedRegs_member (r : Nat) (h : fixtureSavedRegs r = true) : r ∈ countdownMachineConfig.calleeSavedRegs := by
 have r24 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 24 = 24 := by with_unfolding_all rfl
 have r25 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 25 = 25 := by with_unfolding_all rfl
 have r26 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 26 = 26 := by with_unfolding_all rfl
 simpa [fixtureSavedRegs,r24,r25,r26,countdownMachineConfig] using h

theorem configuredTargetLab_assumptions (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) (ms : RiscV.L3.riscv_state)
 (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
 (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
 bs code (configuredTargetLab code cfg bs ms) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
 have prev := configuredLab_initAssumptions code cfg bs fits good
 rw [configuredTargetLab_shape]
 unfold Assumptions at prev ⊢
 rcases prev with ⟨a,b,c,d,e,f,g,h,_,_,rest⟩
 refine ⟨a,b,c,d,e,f,g,h,?_,?_,rest⟩
 · intro r i n saved
   exact targetIoRegsCalleeSaved (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms n r i (fixtureSavedRegs_member r saved)
 · intro r n saved
   exact targetCcRegsCalleeSaved (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi ms n r (fixtureSavedRegs_member r saved)

theorem fixtureTargetLab_assumptions (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
 (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
 [4] code (fixtureTargetLab code cfg ms) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
 apply configuredTargetLab_one code cfg ms ▸ configuredTargetLab_assumptions code cfg [4] ms (by decide) good

end SteppedFlapjack.Concrete
