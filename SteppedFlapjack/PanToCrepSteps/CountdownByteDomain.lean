import SteppedFlapjack.PanToCrepSteps.AlignedCompiledCountdown
import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown

/-! A nonempty byte-closed memory region for the corrected countdown setup. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend

/-- A 64 KiB heap region, disjoint from the code entry at address 4096. -/
def countdownExampleByteDomain (a : BitVec 64) : Bool :=
  decide (65536 ≤ a.toNat ∧ a.toNat < 131072)

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

/-- Place the heap bounds in the original RISC-V length registers. -/
def countdownExampleRegs (r : BitVec 5) : BitVec 64 :=
  if r = 11 then 65536 else if r = 13 then 131072 else 0

/-- The byte domain computed by the actual backend register mapping is the
concrete nonempty byte-closed interval. -/
theorem countdownExampleByteDomain_eq (mem : BitVec 64 → BitVec 8) :
    countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem countdownExampleRegs) (fun _ => false) =
      countdownExampleByteDomain := by
  have init := Flapjack.Compiler.Backend.RiscVConfig.riscvPancakeInitOk countdownMachineConfig countdownMachineConfig_fields.1
  have h4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := init.2.1
  have h2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := init.2.2.2.1
  funext a
  simp [countdownStackByteDomain,countdownAsmState,h4,h2,countdownExampleRegs,countdownExampleByteDomain,BitVec.le_def,BitVec.lt_def]

end SteppedFlapjack.PanToCrepSteps
