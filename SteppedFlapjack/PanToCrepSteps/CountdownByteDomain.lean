import SteppedFlapjack.PanToCrepSteps.AlignedCompiledCountdown
import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown

/-! A nonempty byte-closed memory region for the corrected countdown setup. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend

/-- A 128 KiB heap-and-bitmap region, disjoint from the code entry at address 4096. -/
def countdownExampleByteDomain (a : BitVec 64) : Bool :=
  decide (65536 ≤ a.toNat ∧ a.toNat < 196608)

/-- The concrete region is nonempty and lies inside the machine's program domain. -/
theorem countdownExampleByteDomain_facts :
    countdownExampleByteDomain 65536 = true ∧
    (∀ a, countdownExampleByteDomain a = true → 4096 ≤ a.toNat) := by
  constructor
  · decide
  · intro a h
    simp only [countdownExampleByteDomain,decide_eq_true_eq] at h
    omega

/-- The concrete region is closed under the byte-alignment rule required by
`goodInitState`; unlike the former word-only domain, it is nonempty. -/
theorem countdownExampleByteDomain_closed (a : BitVec 64) :
    countdownExampleByteDomain (holByteAlign a) = true → countdownExampleByteDomain a = true := by
  have log : holLOG2 8 = 3 := by
    rw [holLOG2_eq_log2 (by decide)]
    decide
  have bound : (a.toNat / 8) * 8 < 2^64 := by
    have h := Nat.div_mul_le_self a.toNat 8
    have ha := a.isLt
    omega
  have aligned : (holByteAlign a).toNat = (a.toNat / 8) * 8 := by
    simp only [holByteAlign,Nat.reduceDiv,log,holAlign_eq_div,BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt bound
  intro h
  simp only [countdownExampleByteDomain,decide_eq_true_eq,aligned] at h ⊢
  omega

/-- Byte-addressed bitmap storage follows the 64 KiB heap region. -/
def countdownExampleBitmapsDomain (a : BitVec 64) : Bool :=
  decide (131072 ≤ a.toNat ∧ a.toNat < 196608)

/-- Place the heap bounds in the original RISC-V length registers. -/
def countdownExampleRegs (r : BitVec 5) : BitVec 64 :=
  if r = 11 then 65536 else if r = 13 then 131072 else 0

/-- The byte domain computed by the actual backend register mapping is the
concrete nonempty byte-closed interval. -/
theorem countdownExampleByteDomain_eq (mem : BitVec 64 → BitVec 8) :
    countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem countdownExampleRegs) countdownExampleBitmapsDomain =
      countdownExampleByteDomain := by
  have init := Flapjack.Compiler.Backend.RiscVConfig.riscvPancakeInitOk countdownMachineConfig countdownMachineConfig_fields.1
  have h4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := init.2.1
  have h2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := init.2.2.2.1
  funext a
  apply Bool.eq_iff_iff.mpr
  simp [countdownStackByteDomain,countdownAsmState,h4,h2,countdownExampleRegs,
    countdownExampleBitmapsDomain,countdownExampleByteDomain,BitVec.le_def,BitVec.lt_def]
  omega

end SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend

/-- Construct byte memory from word memory so that every aligned word has
exactly the bytes required by the original machine initializer. -/
noncomputable def countdownBytesOfWords (words : BitVec 64 → BitVec 64) (a : BitVec 64) : BitVec 8 :=
  HolByte.getByte a (words (holByteAlign a)) false

/-- The constructed byte and word memories satisfy the initializers
 global word and byte consistency condition. -/
theorem countdownBytesOfWords_consistent (words : BitVec 64 → BitVec 64) :
    ∀ a, ∃ w, countdownBytesOfWords words a = HolByte.getByte a w false ∧
      (fun x => WordLocW.word (words x)) (holByteAlign a) = .word w := by
  intro a
  exact ⟨words (holByteAlign a),rfl,rfl⟩

/-- A code buffer ending before the heap is in program memory and disjoint
from the concrete byte domain. -/
theorem countdownExample_buffer (mem : BitVec 64 → BitVec 8) (bytes : List (BitVec 8)) (cbspace : Nat)
    (fits : bytes.length + cbspace ≤ 61440) :
    ∀ n, n < cbspace → countdownMachineConfig.progAddresses (BitVec.ofNat 64 (n+bytes.length)+4096) ∧
      countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem countdownExampleRegs)
        countdownExampleBitmapsDomain (BitVec.ofNat 64 (n+bytes.length)+4096) ≠ true := by
  intro n hn
  have small : n + bytes.length + 4096 < 65536 := by omega
  have value : (BitVec.ofNat 64 (n+bytes.length)+4096).toNat = n+bytes.length+4096 := by
    simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
    simp
    omega
  constructor
  · change 4096 ≤ (BitVec.ofNat 64 (n+bytes.length)+4096).toNat
    rw [value]
    omega
  · rw [countdownExampleByteDomain_eq]
    simp only [countdownExampleByteDomain,decide_eq_true_eq,ne_eq]
    rw [value]
    omega

end SteppedFlapjack.PanToCrepSteps
