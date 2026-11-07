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

/-- Assembler view of that same machine, with the machine's exact program domain. -/
def countdownAsmState (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64) : AsmState 64 where
  regs := fun n => regs (BitVec.ofNat 5 n)
  fpRegs := fun _ => 0
  mem := mem
  memDomain := countdownMachineConfig.progAddresses
  pc := 4096
  lr := 1
  align := 2
  be := false
  failed := false

set_option maxRecDepth 4096 in
/-- The concrete states satisfy the target relation, configuration, PC and
interference clauses of `goodInitState` for arbitrary memory and registers. -/
theorem countdownMachineState_initialFacts (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64) :
    let ms := countdownMachineState mem regs
    let asm := countdownAsmState mem regs
    targetStateRel countdownMachineConfig.target asm ms ∧
    targetConfigured asm countdownMachineConfig ∧
    asm.pc = countdownMachineConfig.target.getPc ms ∧
    startPcOk countdownMachineConfig asm.pc ∧
    (BitVec.ofNat 64 (2 ^ asm.align - 1) &&& asm.pc) = 0 ∧
    interferenceOk countdownMachineConfig.nextInterfer
      (countdownMachineConfig.target.proj countdownMachineConfig.progAddresses) ∧
    ffiInterferOkHOL asm.pc countdownMachineConfig ∧ ccacheInterferOkHOL asm.pc countdownMachineConfig := by
  dsimp only
  refine ⟨?_,?_,rfl,countdownMachineConfig_startPc,?_,countdownMachineConfig_interference.1,
    countdownMachineConfig_interference.2 _,countdownMachineConfig_ccache _⟩
  · refine ⟨?_,rfl,?_,?_,?_⟩
    · change riscvOk (countdownMachineState mem regs) = true
      apply (riscvOk_iff _).mpr
      refine ⟨rfl,rfl,rfl,rfl,?_⟩
      change holAligned 2 (4096 : BitVec 64) = true
      decide
    · intro a _
      rfl
    · intro i _
      rfl
    · intro i hi
      change i < 0 at hi
      omega
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · change (BitVec.ofNat 64 (2 ^ 2 - 1) &&& (4096 : BitVec 64)) = 0
    decide

/-- A byte layout in the machine's program domain gives the target's actual
code-loading predicate; the exclusion domain is shared with the heap proof. -/
theorem bytesInMem_codeLoaded (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64)
    (bytes : List (BitVec 8)) (excluded : BitVec 64 → Prop)
    (loaded : bytesInMemHOL 4096 bytes mem countdownMachineConfig.progAddresses excluded) :
    codeLoaded bytes countdownMachineConfig (countdownMachineState mem regs) := by
  classical
  have readBytes : ∀ (address : BitVec 64) (bs : List (BitVec 8)),
      bytesInMemHOL address bs mem countdownMachineConfig.progAddresses excluded →
      readBytearrayWordHOL (byteWidth := 8) address bs.length
        (fun a => if countdownMachineConfig.progAddresses a then some (mem a) else none) = some bs := by
    intro address bs
    induction bs generalizing address with
    | nil => simp [readBytearrayWordHOL]
    | cons byte rest ih =>
      intro h
      obtain ⟨domain,_,value,tail⟩ := h
      simp only [List.length_cons,readBytearrayWordHOL,if_pos domain,value,ih _ tail]
      rfl
  exact readBytes 4096 bytes loaded

/-- For the concrete target states and an empty shared domain, only the
physical byte/word layout, heap domain and code-buffer conditions remain. -/
theorem countdownMachineState_goodInit (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64)
    (words : BitVec 64 → WordLocW 64) (dm : BitVec 64 → Bool) (bytes : List (BitVec 8)) (cbspace : Nat)
    (loaded : bytesInMemHOL 4096 bytes mem countdownMachineConfig.progAddresses (fun a => dm a = true))
    (domain : ∀ a, dm a = true → countdownMachineConfig.progAddresses a)
    (closed : ∀ a, dm (holByteAlign a) = true → dm a = true)
    (wordsOk : ∀ a, ∃ w, mem a = HolByte.getByte a w false ∧ words (holByteAlign a) = .word w)
    (buffer : ∀ n, n < cbspace → countdownMachineConfig.progAddresses (BitVec.ofNat 64 (n+bytes.length)+4096) ∧
      dm (BitVec.ofNat 64 (n+bytes.length)+4096) ≠ true)
    (size : cbspace+bytes.length < 2^64) :
    goodInitState countdownMachineConfig (countdownMachineState mem regs) bytes cbspace
      (countdownAsmState mem regs) words dm (fun _ => false) := by
  obtain ⟨rel,configured,pc,start,alignment,interf,ffi,cache⟩ := countdownMachineState_initialFacts mem regs
  refine ⟨rel,configured,pc,start,alignment,interf,ffi,cache,bytesInMem_codeLoaded mem regs bytes _ loaded,?_,
    domain,closed,?_,?_,?_,?_,?_,size⟩
  · exact loaded
  · funext a
    simp [countdownMachineConfig]
  · intro a h
    cases h
  · simp [countdownMachineConfig,Set.disjoint_left]
  · exact wordsOk
  · exact buffer

end SteppedFlapjack.PanToCrepSteps
