import SteppedFlapjack.Concrete.FixtureTargetLab
import SteppedFlapjack.PanToCrepSteps.CountdownMachineState

/-! RISC-V and assembler states for the loaded init-e-shaped fixture. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.PanToCrepSteps

/-- Physical registers agree with the Lab fixture at all machine registers. -/
def fixtureMachineRegs (r : BitVec 5) : BitVec 64 := fixtureAsm.regs r.toNat

/-- Byte memory obtained from the fixture's loaded word-backed memory. -/
noncomputable def fixtureMachineBytes (code : List (Nat × HolProg 64)) : BitVec 64 → BitVec 8 :=
  countdownBytesOfWords (fixtureLoadedWords (fixtureCodeStart code) (fixtureCodeBytes code))

/-- Concrete RISC-V state with compiled code and the original fixture registers. -/
noncomputable def fixtureMachineState (code : List (Nat × HolProg 64)) : RiscV.L3.riscv_state :=
  { countdownMachineState (fixtureMachineBytes code) fixtureMachineRegs with
    c_PC := fun _ => fixtureCodeStart code }

/-- Assembler state reading the exact same registers and bytes as the machine. -/
noncomputable def fixtureMachineAsm (code : List (Nat × HolProg 64)) : AsmState 64 :=
  { fixtureAsm with
    mem := fixtureMachineBytes code
    memDomain := (fixtureMachineConfig (fixtureCodeStart code)).progAddresses
    pc := fixtureCodeStart code
    align := 2 }

set_option maxRecDepth 10000 in
/-- Machine registers and memory satisfy the target relation whenever the entry
address meets the target's ordinary instruction-alignment condition. -/
theorem fixtureMachineState_targetRel (code : List (Nat × HolProg 64))
    (aligned : holAligned 2 (fixtureCodeStart code) = true) :
    targetStateRel riscvTarget (fixtureMachineAsm code) (fixtureMachineState code) := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · change riscvOk (fixtureMachineState code) = true
    apply (riscvOk_iff _).mpr
    exact ⟨rfl,rfl,rfl,rfl,aligned⟩
  · intro a _
    rfl
  · intro i hi
    change fixtureMachineRegs (BitVec.ofNat 5 i) = fixtureAsm.regs i
    unfold fixtureMachineRegs
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by change i < 32; exact hi.1)]
  · intro i hi
    change i < 0 at hi
    omega


/-- Each byte of a small compiled program lies between its entry and buffer. -/
theorem fixtureCodeAddress_bounds (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) (i : Nat) (hi : i < (fixtureCodeBytes code).length) :
    let pc := fixtureCodeStart code
    pc.toNat ≤ (pc + BitVec.ofNat 64 i).toNat ∧
    0x80000000 ≤ (pc + BitVec.ofNat 64 i).toNat ∧
    (pc + BitVec.ofNat 64 i).toNat < 0x800f0134 := by
  dsimp only
  have pc := fixtureCodeStart_toNat code (by omega)
  have idx : i < 2^64 := by omega
  have sum : (fixtureCodeStart code).toNat + i < 2^64 := by omega
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt idx,Nat.mod_eq_of_lt sum]
  omega

set_option maxRecDepth 10000 in
/-- The actual compiled byte stream is loaded at the concrete machine entry. -/
theorem fixtureMachine_codeLoaded (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    bytesInMemHOL (fixtureCodeStart code) (fixtureCodeBytes code) (fixtureMachineBytes code)
      (fixtureMachineConfig (fixtureCodeStart code)).progAddresses
      (fun a => fixtureByteDomain a = true) := by
  apply bytesInMem_of_indexed
  intro i hi
  obtain ⟨entry,lo,hiAddr⟩ := fixtureCodeAddress_bounds code fits i hi
  have shared := fixtureSharedByteDomain_false_between
    (fixtureCodeStart code + BitVec.ofNat 64 i) lo (by omega)
  have data := fixtureByteDomain_false_below (fixtureCodeStart code + BitVec.ofNat 64 i) (by omega)
  refine ⟨⟨entry,shared⟩,?_,?_⟩
  · intro h
    rw [data] at h
    cases h
  · exact fixtureLoadedWords_get (fixtureCodeStart code) (fixtureCodeBytes code) i hi (by omega)

end SteppedFlapjack.Concrete
