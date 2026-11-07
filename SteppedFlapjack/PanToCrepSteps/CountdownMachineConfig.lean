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

/-- The concrete record has exactly the machine configuration required by the
original Pancake RISC-V backend, and contains no FFI or MMIO entries. -/
theorem countdownMachineConfig_fields :
    isRiscvMachineConfig countdownMachineConfig ∧
      countdownMachineConfig.ffiNames = [] ∧ countdownMachineConfig.mmioInfo = [] := by
  exact ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

/-- The fixed entry and reserved service addresses satisfy the full initial
program-counter contract, including the empty FFI boundary. -/
theorem countdownMachineConfig_startPc : startPcOk countdownMachineConfig (4096 : BitVec 64) := by
  have index : mmioPcsMinIndex [] = some 0 := by
    apply mmioPcsMinIndex_eq_some
    simp [mmioIndexBoundary]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,0,?_,?_,?_,?_⟩
  · change ¬ 4096 ≤ (4080 : BitVec 64).toNat
    decide
  · change ¬ 4096 ≤ (4064 : BitVec 64).toNat
    decide
  · simp [countdownMachineConfig]
  · simp [countdownMachineConfig]
  · change (4096 : BitVec 64) - BitVec.ofNat 64 ffiOffset = 4080
    decide
  · change (4096 : BitVec 64) - BitVec.ofNat 64 (2 * ffiOffset) = 4064
    decide
  · decide
  · exact index
  · simp
  · simp [countdownMachineConfig]
  · rfl

/-- Empty FFI and identity ordinary interference satisfy their full contracts. -/
theorem countdownMachineConfig_interference :
    interferenceOk countdownMachineConfig.nextInterfer
      (countdownMachineConfig.target.proj countdownMachineConfig.progAddresses) ∧
    ∀ pc, ffiInterferOkHOL pc countdownMachineConfig := by
  constructor
  · intro i state
    rfl
  · intro pc state k index newBytes asm bytes bytes2 i h
    simp [countdownMachineConfig] at h

set_option maxRecDepth 4096 in
/-- Cache flush returns to the saved link address while preserving registers and memory. -/
theorem countdownMachineConfig_ccache (pc : BitVec 64) :
    ccacheInterferOkHOL pc countdownMachineConfig := by
  intro state asm k a1 a2 ⟨rel,aligned⟩
  have ok : riscvOk state = true := rel.1
  have regs := rel.2.2.2.1
  have link : state.c_gpr state.procID 1 = asm.regs 1 := by
    have h := regs 1 (by decide)
    exact h
  have valid := (riscvOk_iff state).mp ok
  refine ⟨?_,?_,?_,?_⟩
  · apply (riscvOk_iff _).mpr
    refine ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,?_⟩
    simp only [countdownMachineConfig]
    rw [link]
    exact aligned
  · simpa [countdownMachineConfig,riscvTarget,riscvConfig] using link
  · intro a ha
    exact rel.2.2.1 a ha
  · intro r hr
    exact regs r ⟨hr.2.1,by simpa using hr.2.2⟩

end SteppedFlapjack.PanToCrepSteps
