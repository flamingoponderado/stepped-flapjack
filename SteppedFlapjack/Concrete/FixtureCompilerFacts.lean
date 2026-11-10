import SteppedFlapjack.Concrete.CountdownEncoding
import SteppedFlapjack.Concrete.BranchingLabBounds
import SteppedFlapjack.Concrete.FixtureMachineLab

/-! Kernel-checked label removal and size facts for concrete witness programs. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Phase6

/-- Related label-removal results have identical success, byte length, labels,
and shared-memory metadata. -/
theorem relatedCompilerResults (r s : Option (LabSem.LabProgHOL 64 × Spt (Spt Nat)))
    (related : OptRel r s) :
    r.isSome = s.isSome ∧
    (progToBytes (r.getD ([],.ln)).1).length = (progToBytes (s.getD ([],.ln)).1).length ∧
    (r.getD ([],.ln)).2 = (s.getD ([],.ln)).2 ∧
    getShmemInfo (r.getD ([],.ln)).1 0 [] [] = getShmemInfo (s.getD ([],.ln)).1 0 [] [] := by
  cases related with
  | none => simp
  | some c c' labs related =>
    exact ⟨rfl,progToBytes_length_rel related,rfl,getShmemInfo_rel related 0 [] []⟩

/-- Transfer concrete compiler facts across same-length encodings. -/
theorem fixtureCompilerFacts_transfer (code other : List (Nat × StackLang.HolProg 64))
    (related : OptRel (fixtureRemoveLabels code) (fixtureRemoveLabels other))
    (facts : (fixtureRemoveLabels other).isSome = true ∧
      (fixtureCodeBytes other).length ≤ 0xecc ∧ (fixtureCodeBytes other).length % 4 = 0) :
    (fixtureRemoveLabels code).isSome = true ∧
      (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0 := by
  obtain ⟨success,length,_,_⟩ := relatedCompilerResults _ _ related
  have size : (fixtureCodeBytes code).length = (fixtureCodeBytes other).length := by
    rw [fixtureCompiled_bytes code,fixtureCompiled_bytes other]
    exact length
  exact ⟨success.trans facts.1,by rw [size]; exact facts.2.1,by rw [size]; exact facts.2.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Concrete label-removal success, code fit, and instruction alignment. -/
theorem countdownZero_compiler_facts :
    (fixtureRemoveLabels (countdownNativeStackCode 0)).isSome = true ∧
    (fixtureCodeBytes (countdownNativeStackCode 0)).length ≤ 0xecc ∧
    (fixtureCodeBytes (countdownNativeStackCode 0)).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels
    change (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
        riscvConfig.addrOffset (countdownNativeStackCode 0)))).isSome = true
    rw [countdown_nativeShape]
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    rw [countdown_nativeShape]
    simp_rw [progToBytesMap]
    with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Concrete label-removal success, code fit, and instruction alignment. -/
theorem countdown2048_compiler_facts :
    (fixtureRemoveLabels (countdownNativeStackCode 2048)).isSome = true ∧
    (fixtureCodeBytes (countdownNativeStackCode 2048)).length ≤ 0xecc ∧
    (fixtureCodeBytes (countdownNativeStackCode 2048)).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels
    change (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
        riscvConfig.addrOffset (countdownNativeStackCode 2048)))).isSome = true
    rw [countdown_nativeShape]
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    rw [countdown_nativeShape]
    simp_rw [progToBytesMap]
    with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Concrete label-removal success, code fit, and instruction alignment. -/
theorem countdownLarge_compiler_facts :
    (fixtureRemoveLabels (countdownNativeStackCode (2^31))).isSome = true ∧
    (fixtureCodeBytes (countdownNativeStackCode (2^31))).length ≤ 0xecc ∧
    (fixtureCodeBytes (countdownNativeStackCode (2^31))).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels
    change (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
        riscvConfig.addrOffset (countdownNativeStackCode (2^31))))).isSome = true
    rw [countdown_nativeShape]
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    rw [countdown_nativeShape]
    simp_rw [progToBytesMap]
    with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Concrete label-removal success, code fit, and instruction alignment. -/
theorem comparison_compiler_facts :
    (fixtureRemoveLabels (comparisonNativeCode)).isSome = true ∧
    (fixtureCodeBytes (comparisonNativeCode)).length ≤ 0xecc ∧
    (fixtureCodeBytes (comparisonNativeCode)).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels
    change (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
        riscvConfig.addrOffset (comparisonNativeCode)))).isSome = true
    unfold comparisonNativeCode
    rw [comparison_optimized_table,riscvNative_two_entry_code]
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    unfold comparisonNativeCode
    rw [comparison_optimized_table,riscvNative_two_entry_code]
    simp_rw [progToBytesMap]
    with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Concrete label-removal success, code fit, and instruction alignment. -/
theorem branching_compiler_facts :
    (fixtureRemoveLabels (branchingLoopNativeCode)).isSome = true ∧
    (fixtureCodeBytes (branchingLoopNativeCode)).length ≤ 0xecc ∧
    (fixtureCodeBytes (branchingLoopNativeCode)).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels
    change (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
        riscvConfig.addrOffset (branchingLoopNativeCode)))).isSome = true
    unfold branchingLoopNativeCode
    rw [branch_optimized_table,riscvNative_two_entry_code]
    with_unfolding_all decide
  · unfold fixtureCodeBytes
    unfold branchingLoopNativeCode
    rw [branch_optimized_table,riscvNative_two_entry_code]
    simp_rw [progToBytesMap]
    with_unfolding_all decide


/-- All countdown inputs compile to fitting, aligned RISC-V code. -/
theorem countdown_compiler_facts (n : Nat) :
    (fixtureRemoveLabels (countdownNativeStackCode n)).isSome = true ∧
    (fixtureCodeBytes (countdownNativeStackCode n)).length ≤ 0xecc ∧
    (fixtureCodeBytes (countdownNativeStackCode n)).length % 4 = 0 := by
  rcases countdown_removeLabels_cases n countdownRiscVBackend.labConf with h | h | h
  · exact fixtureCompilerFacts_transfer _ _ h countdownZero_compiler_facts
  · exact fixtureCompilerFacts_transfer _ _ h countdown2048_compiler_facts
  · exact fixtureCompilerFacts_transfer _ _ h countdownLarge_compiler_facts

end SteppedFlapjack.Concrete
