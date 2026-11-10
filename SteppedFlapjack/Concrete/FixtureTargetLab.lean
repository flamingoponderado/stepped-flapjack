import SteppedFlapjack.Concrete.InitEStack
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.Semantics.TargetProps.CalleeSaved
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.Semantics.TargetProps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.Concrete

/-- Assembly register inputs for the aligned init-e-shaped Lab layout. -/
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
 LabToTarget.makeInit countdownMachineConfig sourceFfi fixtureAsm fixtureLabMemory (fun a => decide (fixtureLabDomain a))
  (fun a => decide (sharedAddress a)) ms (fixtureLab code cfg).code (fun _ _ => none) 0x800f0134 0xecc
  (fixtureLab code cfg).compileOracle

theorem fixtureTargetLab_shape (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state) :
 fixtureTargetLab code cfg ms = {(fixtureLab code cfg) with
  ioRegs := targetIoRegs countdownMachineConfig sourceFfi ms,
  ioFpRegs := targetIoFpRegs countdownMachineConfig sourceFfi ms,
  ccRegs := targetCcRegs countdownMachineConfig sourceFfi ms,
  ccFpRegs := targetCcFpRegs countdownMachineConfig sourceFfi ms} := by
 unfold fixtureTargetLab LabToTarget.makeInit fixtureLab
 congr 1
 all_goals try (with_unfolding_all rfl)
 funext r
 simp only [fixtureAsm,fixtureLabRegs]
 repeat' first | split | simp_all
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

theorem fixtureTargetLab_stack (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state) :
 (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset
  [4] code (fixtureTargetLab code cfg ms) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1 = fixtureStack code cfg := by
 rw [fixtureTargetLab_shape]
 unfold fixtureStack
 rw [fullMakeInit_eq,fullMakeInit_eq]
 rfl

private theorem fixtureSavedRegs_member (r : Nat) (h : fixtureSavedRegs r = true) : r ∈ countdownMachineConfig.calleeSavedRegs := by
 have r24 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 24 = 24 := by with_unfolding_all rfl
 have r25 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 25 = 25 := by with_unfolding_all rfl
 have r26 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 26 = 26 := by with_unfolding_all rfl
 simpa [fixtureSavedRegs,r24,r25,r26,countdownMachineConfig] using h

theorem fixtureTargetLab_assumptions (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
 (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset
 [4] code (fixtureTargetLab code cfg ms) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
 have prev := fixtureLab_initAssumptions code cfg good
 rw [fixtureTargetLab_shape]
 unfold Assumptions at prev ⊢
 rcases prev with ⟨a,b,c,d,e,f,g,h,_,_,rest⟩
 refine ⟨a,b,c,d,e,f,g,h,?_,?_,rest⟩
 · intro r i n saved
   exact targetIoRegsCalleeSaved countdownMachineConfig sourceFfi ms n r i (fixtureSavedRegs_member r saved)
 · intro r n saved
   exact targetCcRegsCalleeSaved countdownMachineConfig sourceFfi ms n r (fixtureSavedRegs_member r saved)

end SteppedFlapjack.Concrete
