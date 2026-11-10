import SteppedFlapjack.LabToTargetSteps.DomainAlignmentBridge
import SteppedFlapjack.LoopToWordSteps.FullInitMachineConstruct

/-! Explicit Lab-to-RISC-V clock bound from the original machine initializer. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps

/-- A terminating aligned Lab run from the actual initializer yields the same
outcome and FFI state on the initialized RISC-V machine at a calculable clock. -/
theorem initializedLabToRiscVExplicit {F : Type}
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState F) (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (oracle : Nat → Config × LabProgHOL 64)
    (names : List HolFfiName) (info newInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (guards : LabMachineInitGuards mc machine (LabFilter.filterSkip code) code2 labs labelClock i cbspace
      asm memory dm sdm (fun n => ((oracle n).1,LabFilter.filterSkip (oracle n).2)) names info newInfo)
    (clock bound : Nat) (outcome : HolOutcome) (post : LabSem.State 64 Config F)
    (run : evaluate {LabProps.alignDm (makeInit mc ffi asm memory dm sdm machine code
      (LabToTarget.compile mc.target.config) (mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length)
      cbspace oracle) with clock := clock} = (.halt outcome,post)) (hbound : clock ≤ bound) :
    ∃ finalMachine, evaluateTargetHOL mc ffi
      (labTickBound 4 code2 ⟨mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length,[],cbspace⟩ * bound)
      machine = (.halt outcome,finalMachine,post.ffi) := by
  let cbpos := mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length
  let original := makeInit mc ffi asm memory dm sdm machine code (LabToTarget.compile mc.target.config) cbpos cbspace oracle
  let filteredOracle := fun n => ((oracle n).1, LabFilter.filterSkip (oracle n).2)
  let filtered := makeInit mc ffi asm memory dm sdm machine (LabFilter.filterSkip code)
    (compileLab mc.target.config) cbpos cbspace filteredOracle
  have rel := makeInit_stateRel mc machine ffi (LabFilter.filterSkip code) code2 labs labelClock i cbspace
    asm memory dm sdm filteredOracle names info newInfo guards
  have tie := oracleTie_makeInit mc ffi asm memory dm sdm machine (LabFilter.filterSkip code)
    (compileLab mc.target.config) cbpos cbspace filteredOracle
  have filterRel := makeInit_filterRel mc ffi asm memory dm sdm machine code
    (compileLab mc.target.config) cbpos cbspace oracle
  have link : LabExecutionLink filtered (alignDm original) := Or.inr (Or.inr ⟨original,rfl,by exact filterRel⟩)
  have result := connectedLabToRiscVExplicit (mc.target.getPc machine) filtered (alignDm original) post
    outcome clock bound mc code2 labs asm machine hmc link tie rel run hbound
  simpa [filtered,original,makeInit,alignDm,cbpos] using result

end SteppedFlapjack.LabToTargetSteps
