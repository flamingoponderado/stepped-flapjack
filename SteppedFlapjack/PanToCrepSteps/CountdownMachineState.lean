import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig

/-! Concrete RISC-V and assembler initial states for the countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Build a valid 64-bit RISC-V state at the countdown entry point. Memory
and general registers remain explicit so they can contain code and heap data. -/
def countdownMachineState (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64) : RiscV.L3.riscv_state :=
  { (default : RiscV.L3.riscv_state) with
    MEM8 := mem
    c_gpr := fun _ => regs
    c_PC := fun _ => 4096
    c_NextFetch := fun _ => none
    c_MCSR := fun _ => { (default : RiscV.L3.MachineCSR) with
      mstatus := { (default : RiscV.L3.mstatus) with VM := 0 },
      mcpuid := { (default : RiscV.L3.mcpuid) with ArchBase := 2 } }
    exception := .NoException }

/-- A sequential byte assertion can be read back from its domain. -/
theorem bytesInMem_readBytes (mem : BitVec 64 → BitVec 8) (domain excluded : BitVec 64 → Prop) [DecidablePred domain]
    (address : BitVec 64) (bytes : List (BitVec 8))
    (loaded : bytesInMemHOL address bytes mem domain excluded) :
    readBytearrayWordHOL (byteWidth := 8) address bytes.length
      (fun a => if domain a then some (mem a) else none) = some bytes := by
  classical
  induction bytes generalizing address with
  | nil => simp [readBytearrayWordHOL]
  | cons byte rest ih =>
    obtain ⟨inside,_,value,tail⟩ := loaded
    simp only [List.length_cons,readBytearrayWordHOL,if_pos inside,value,ih _ tail]
    rfl

end SteppedFlapjack.PanToCrepSteps
