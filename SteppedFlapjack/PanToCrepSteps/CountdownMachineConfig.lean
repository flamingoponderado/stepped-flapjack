import SteppedFlapjack.PanToCrepSteps.NoFfiCountdown

/-! A concrete empty-FFI RISC-V machine configuration for the countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target

/-- Code addresses start at 4096; halt and cache-flush entry points are
reserved immediately below them. Cache flush returns through the link register. -/
noncomputable def countdownMachineConfig : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection where
  progAddresses := fun a => 4096 ≤ a.toNat
  sharedAddresses := fun _ => False
  ffiEntryPcs := []
  ffiNames := []
  ptrReg := 10
  lenReg := 11
  ptr2Reg := 12
  len2Reg := 13
  ffiInterfer := fun _ input => input.2.2
  calleeSavedRegs := [24,25,26]
  nextInterfer := fun _ state => state
  haltPc := 4080
  ccachePc := 4064
  ccacheInterfer := fun _ input =>
    let state := input.2.2
    { state with c_PC := fun pid => if pid = state.procID then state.c_gpr state.procID 1 else state.c_PC pid }
  target := riscvTarget
  mmioInfo := []

end SteppedFlapjack.PanToCrepSteps
