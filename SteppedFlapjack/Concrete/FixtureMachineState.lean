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

/-- Loaded machine bytes for the exact compiler-provided bitmap list. -/
noncomputable def configuredMachineBytes (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) : BitVec 64 → BitVec 8 :=
  countdownBytesOfWords (countdownWriteCode (fixtureCodeStart code) (fixtureCodeBytes code)
    (bitmapInitialWords bs (initialWordFor bs.length)))

noncomputable def configuredMachineState (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) : RiscV.L3.riscv_state :=
  { countdownMachineState (configuredMachineBytes code bs) fixtureMachineRegs with
    c_PC := fun _ => fixtureCodeStart code }

noncomputable def configuredMachineAsm (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) : AsmState 64 :=
  { fixtureAsm with
    mem := configuredMachineBytes code bs
    memDomain := (fixtureMachineConfig (fixtureCodeStart code)).progAddresses
    pc := fixtureCodeStart code
    align := 2 }

theorem configuredMachineBytes_one (code : List (Nat × HolProg 64)) :
    configuredMachineBytes code [4] = fixtureMachineBytes code := by
  unfold configuredMachineBytes fixtureMachineBytes fixtureLoadedWords
  change countdownBytesOfWords (countdownWriteCode _ _ (bitmapInitialWords [4] (initialWordFor 1))) = _
  rw [initialWordFor_one, bitmapInitialWords_singleton]

theorem configuredMachineState_one (code : List (Nat × HolProg 64)) :
    configuredMachineState code [4] = fixtureMachineState code := by
  unfold configuredMachineState fixtureMachineState
  rw [configuredMachineBytes_one]

theorem configuredMachineAsm_one (code : List (Nat × HolProg 64)) :
    configuredMachineAsm code [4] = fixtureMachineAsm code := by
  unfold configuredMachineAsm fixtureMachineAsm
  rw [configuredMachineBytes_one]

set_option maxRecDepth 10000 in
theorem configuredMachineState_targetRel (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (aligned : holAligned 2 (fixtureCodeStart code) = true) :
    targetStateRel riscvTarget (configuredMachineAsm code bs) (configuredMachineState code bs) := by
  refine ⟨?_,rfl,?_,?_,?_⟩
  · change riscvOk (configuredMachineState code bs) = true
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

set_option maxRecDepth 10000 in
/-- Machine registers and memory satisfy the target relation whenever the entry
address meets the target's ordinary instruction-alignment condition. -/
theorem fixtureMachineState_targetRel (code : List (Nat × HolProg 64))
    (aligned : holAligned 2 (fixtureCodeStart code) = true) :
    targetStateRel riscvTarget (fixtureMachineAsm code) (fixtureMachineState code) := by
  have h := configuredMachineState_targetRel code [4] aligned
  rwa [configuredMachineAsm_one, configuredMachineState_one] at h


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

theorem configuredLabMemory_eq_loaded (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) (a : BitVec 64) :
    configuredLabMemory code bs a = .word (countdownWriteCode (fixtureCodeStart code) (fixtureCodeBytes code)
      (bitmapInitialWords bs (initialWordFor bs.length)) a) := by
  by_cases domain : configuredLabDomain bs a
  · simp only [configuredLabMemory,if_pos domain]
    exact (bitmapLoadedWords_domain (fixtureCodeStart code) (fixtureCodeBytes code) bs (initialWordFor bs.length)
      (fixtureCodeStart_fits code fits) a domain).symm
  · simp [configuredLabMemory,domain]

set_option maxRecDepth 10000 in
/-- The actual compiled byte stream is loaded at the concrete machine entry. -/
theorem configuredMachine_codeLoaded (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    bytesInMemHOL (fixtureCodeStart code) (fixtureCodeBytes code) (configuredMachineBytes code bs)
      (fixtureMachineConfig (fixtureCodeStart code)).progAddresses
      (fun a => configuredByteDomain bs a = true) := by
  apply bytesInMem_of_indexed
  intro i hi
  obtain ⟨entry,lo,hiAddr⟩ := fixtureCodeAddress_bounds code fits i hi
  have shared := fixtureSharedByteDomain_false_between
    (fixtureCodeStart code + BitVec.ofNat 64 i) lo (by omega)
  have data := configuredByteDomain_false_below bs (fixtureCodeStart code + BitVec.ofNat 64 i) (by omega)
  refine ⟨⟨entry,shared⟩,?_,?_⟩
  · intro h
    rw [data] at h
    cases h
  · exact countdownWriteCode_get (fixtureCodeBytes code) (fixtureCodeStart code) (bitmapInitialWords bs (initialWordFor bs.length)) i hi (by omega)


/-- The machine semantics sees exactly the loaded compiler byte stream. -/
theorem configuredMachine_targetCodeLoaded (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    codeLoaded (fixtureCodeBytes code) (fixtureMachineConfig (fixtureCodeStart code))
      (configuredMachineState code bs) := by
  classical
  exact bytesInMem_readBytes (configuredMachineBytes code bs)
    (fixtureMachineConfig (fixtureCodeStart code)).progAddresses (fun a => configuredByteDomain bs a = true)
    (fixtureCodeStart code) (fixtureCodeBytes code) (configuredMachine_codeLoaded code bs fits)


/-- Every byte in the reserved code buffer is program memory outside data. -/
theorem configuredMachine_codeBuffer (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    ∀ n, n < 0xecc →
      (configuredMachineAsm code bs).memDomain
        (BitVec.ofNat 64 (n+(fixtureCodeBytes code).length) + fixtureCodeStart code) ∧
      configuredByteDomain bs (BitVec.ofNat 64 (n+(fixtureCodeBytes code).length) + fixtureCodeStart code) ≠ true := by
  intro n hn
  have pos : BitVec.ofNat 64 (n+(fixtureCodeBytes code).length) + fixtureCodeStart code =
      (0x800f0134 : BitVec 64) + BitVec.ofNat 64 n := by
    rw [BitVec.ofNat_add]
    rw [add_comm (BitVec.ofNat 64 n) (BitVec.ofNat 64 (fixtureCodeBytes code).length),
      add_assoc,add_comm (BitVec.ofNat 64 n) (fixtureCodeStart code),← add_assoc,
      add_comm (BitVec.ofNat 64 (fixtureCodeBytes code).length) (fixtureCodeStart code),
      fixtureCodeStart_add_length]
  have addr : ((0x800f0134 : BitVec 64) + BitVec.ofNat 64 n).toNat = 0x800f0134 + n := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    have small : n < 2^64 := by omega
    rw [Nat.mod_eq_of_lt small]
    have addSmall : 0x800f0134 + n < 2^64 := by omega
    change (0x800f0134 + n) % 2^64 = _
    rw [Nat.mod_eq_of_lt addSmall]
  rw [pos]
  have pc := fixtureCodeStart_toNat code (by omega)
  have shared := fixtureSharedByteDomain_false_between ((0x800f0134 : BitVec 64) + BitVec.ofNat 64 n)
    (by rw [addr]; omega) (by rw [addr]; omega)
  have data := configuredByteDomain_false_below bs ((0x800f0134 : BitVec 64) + BitVec.ofNat 64 n)
    (by rw [addr]; omega)
  constructor
  · exact ⟨by rw [addr]; omega,shared⟩
  · intro h
    rw [data] at h
    cases h


set_option maxRecDepth 10000 in
/-- The actual compiled byte stream is loaded at the concrete machine entry. -/
theorem fixtureMachine_codeLoaded (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    bytesInMemHOL (fixtureCodeStart code) (fixtureCodeBytes code) (fixtureMachineBytes code)
      (fixtureMachineConfig (fixtureCodeStart code)).progAddresses
      (fun a => fixtureByteDomain a = true) := by
  have h := configuredMachine_codeLoaded code [4] fits
  rwa [configuredMachineBytes_one, configuredByteDomain_one] at h


/-- The machine semantics sees exactly the loaded compiler byte stream. -/
theorem fixtureMachine_targetCodeLoaded (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    codeLoaded (fixtureCodeBytes code) (fixtureMachineConfig (fixtureCodeStart code))
      (fixtureMachineState code) := by
  have h := configuredMachine_targetCodeLoaded code [4] fits
  rwa [configuredMachineState_one] at h


/-- Every byte in the reserved code buffer is program memory outside data. -/
theorem fixtureMachine_codeBuffer (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    ∀ n, n < 0xecc →
      (fixtureMachineAsm code).memDomain
        (BitVec.ofNat 64 (n+(fixtureCodeBytes code).length) + fixtureCodeStart code) ∧
      fixtureByteDomain (BitVec.ofNat 64 (n+(fixtureCodeBytes code).length) + fixtureCodeStart code) ≠ true := by
  have h := configuredMachine_codeBuffer code [4] fits
  rwa [configuredMachineAsm_one, configuredByteDomain_one] at h


/-- Encoded instruction-size alignment gives the bit-mask contracts required
by the assembler and target machine. -/
theorem fixtureCodeStart_masks (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440)
    (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    (3 &&& fixtureCodeStart code) = 0 ∧ (1 &&& fixtureCodeStart code) = 0 := by
  have h4 := fixtureCodeStart_aligned code (by omega) aligned
  have h2 : (fixtureCodeStart code).toNat % 2 = 0 := by omega
  constructor <;> apply BitVec.eq_of_toNat_eq
  · rw [BitVec.toNat_and]
    change 3 &&& (fixtureCodeStart code).toNat = 0
    rw [Nat.and_comm]
    change (fixtureCodeStart code).toNat &&& (2^2-1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact h4
  · rw [BitVec.toNat_and]
    change 1 &&& (fixtureCodeStart code).toNat = 0
    rw [Nat.and_comm]
    change (fixtureCodeStart code).toNat &&& (2^1-1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact h2


set_option maxRecDepth 10000 in
/-- A fitting, instruction-aligned compiler output satisfies the complete
machine initialization contract with the byte-closed fixture domains. -/
theorem configuredMachine_goodInit (code : List (Nat × HolProg 64)) (bs : List (BitVec 64))
    (bitmapFits : 0xa0020018 + bs.length * 8 ≤ 0xa0410000)
    (fits : (fixtureCodeBytes code).length ≤ 61440)
    (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    goodInitState (fixtureMachineConfig (fixtureCodeStart code)) (configuredMachineState code bs)
      (fixtureCodeBytes code) 0xecc (configuredMachineAsm code bs) (configuredLabMemory code bs)
      (configuredByteDomain bs) fixtureSharedByteDomain := by
  have masks := fixtureCodeStart_masks code fits aligned
  have haligned : holAligned 2 (fixtureCodeStart code) = true := by
    rw [Flapjack.holAligned_iff]
    exact fixtureCodeStart_aligned code (by omega) aligned
  have pc := fixtureCodeStart_toNat code (by omega)
  have low : 0x80000020 ≤ (fixtureCodeStart code).toNat := by omega
  have high : (fixtureCodeStart code).toNat < 0xa0410000 := by omega
  have pcBound : (fixtureCodeStart code).toNat ≤ 0xa0020018 := by omega
  have services := fixtureMachineConfig_interference (fixtureCodeStart code)
  refine ⟨configuredMachineState_targetRel code bs haligned,?_,rfl,
    fixtureMachineConfig_startPc _ low high masks.2,?_,services.1,services.2 _,
    fixtureMachineConfig_ccache _ _,configuredMachine_targetCodeLoaded code bs fits,?_,?_,
    configuredByteDomain_closed bs,?_,fixtureSharedByteDomain_closed,fixtureMachineConfig_disjoint _,?_,
    configuredMachine_codeBuffer code bs fits,?_⟩
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · change (3 &&& fixtureCodeStart code) = 0
    exact masks.1
  · exact configuredMachine_codeLoaded code bs fits
  · intro a h
    exact configuredByteDomain_in_program bs _ a bitmapFits pcBound h
  · rfl
  · intro a
    refine ⟨countdownWriteCode (fixtureCodeStart code) (fixtureCodeBytes code) (bitmapInitialWords bs (initialWordFor bs.length)) (holByteAlign a),rfl,?_⟩
    exact configuredLabMemory_eq_loaded code bs fits _
  · omega


set_option maxRecDepth 10000 in
/-- A fitting, instruction-aligned compiler output satisfies the complete
machine initialization contract with the byte-closed fixture domains. -/
theorem fixtureMachine_goodInit (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440)
    (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    goodInitState (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
      (fixtureCodeBytes code) 0xecc (fixtureMachineAsm code) (fixtureLabMemoryFor code)
      fixtureByteDomain fixtureSharedByteDomain := by
  have memEq := congrArg (fun lab => lab.memory) (configuredLab_one code countdownRiscVBackend.labConf)
  change configuredLabMemory code [4] = fixtureLabMemoryFor code at memEq
  have h := configuredMachine_goodInit code [4] (by decide) fits aligned
  rwa [configuredMachineState_one, configuredMachineAsm_one, memEq, configuredByteDomain_one] at h

end SteppedFlapjack.Concrete
