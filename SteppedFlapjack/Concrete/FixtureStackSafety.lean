import SteppedFlapjack.Concrete.FixtureCompilerFacts
import SteppedFlapjack.LabToTargetSteps.FfiFreeFlatten
import SteppedFlapjack.LabToTargetSteps.GoodCodeFilter
import SteppedFlapjack.PanToCrepSteps.CountdownGoodCode
import Flapjack.Compiler.Backend.StackToLab.Proofs.NoShmemop
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyGoodCodeSource

/-! The concrete native programs have neither FFI nor shared-memory operations. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LabToTargetSteps

/-- Executable structural check on each native Stack function. -/
def fixtureStackSafe (code : List (Nat × HolProg 64)) : Bool :=
  code.all (fun row => noShmemop row.2 && stackNoFfi row.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual source compiler establishes the Lab good-code guard. -/
theorem singleEntry_labGoodCode (body : Flapjack.Pancake.PanLang.ProgHOL 64)
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (compiled : panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main") body) = words)
    (sourceGood : pancakeGoodCodeHOL (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main") body) = true) :
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false
          (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2
        countdownRiscVBackend.labConf).code) := by
  let source := singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main") body
  have nodup : ((Flapjack.Pancake.PanLang.functionsHOL source).map Prod.fst).Nodup := by
    simp [source,singleEntryProgram,Flapjack.Pancake.PanLang.functionsHOL]
  have good := Flapjack.Pancake.Proofs.PanToTarget.panToTargetGoodCodeSource (β := Nat)
    countdownRiscVBackend countdownMachineConfig source (by exact riscvPancakeBackendConfigOk)
    (by simp [goodDimindex]) (by decide) nodup sourceGood
  have whole : goodCode riscvConfig (.ln : Spt (Spt Nat))
      (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
        (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false
          (Flapjack.Compiler.Backend.WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2) := by
    have htarget : countdownMachineConfig.target.config = riscvConfig := rfl
    rw [htarget] at good
    dsimp only [source] at good
    rw [compiled,fixture_backend_maxHeap] at good
    exact good
  exact goodCode_filterSkip riscvConfig (.ln : Spt (Spt Nat)) _ whole

/-- An FFI-free, shared-operation-free native table has the corresponding Lab properties. -/
theorem fixtureLabSafe (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (safe : fixtureStackSafe code = true) :
    noShareMemInst (LabFilter.filterSkip (fixtureLab code cfg).code) ∧
      findFfiNames (LabFilter.filterSkip (fixtureLab code cfg).code) = [] := by
  have rows : ∀ row ∈ code, noShmemop row.2 = true ∧ stackNoFfi row.2 = true := by
    intro row member
    have h := List.all_eq_true.mp safe row member
    simp only [Bool.and_eq_true] at h
    exact h
  constructor
  · apply (LabToTarget.FilterSkip.noShareMemFilterSkip _).2
    apply StackToLab.Proofs.NoShmemop.compileNoShareMemInst code _
    exact ⟨fun row h => (rows row h).1,rfl⟩
  · rw [LabToTarget.FilterSkip.findFfiNamesFilterSkip]
    apply stackToLab_noFfi
    exact fun row h => (rows row h).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem countdownZero_stackSafe : fixtureStackSafe (countdownNativeStackCode 0) = true := by
  unfold fixtureStackSafe
  rw [countdown_nativeShape]
  with_unfolding_all decide

/-- Every countdown input has the same operation-safety check as zero. -/
theorem countdown_stackSafe (n : Nat) : fixtureStackSafe (countdownNativeStackCode n) = true := by
  have same : fixtureStackSafe (countdownNativeStackCode n) = fixtureStackSafe (countdownNativeStackCode 0) := by
    unfold fixtureStackSafe
    rw [countdown_nativeShape n,countdown_nativeShape 0]
    simp [SteppedFlapjack.Phase6.prefixCode,SteppedFlapjack.Phase6.P,noShmemop,stackNoFfi]
  rw [same]
  exact countdownZero_stackSafe

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The comparison witness is FFI-free and has no shared-memory operation. -/
theorem comparison_stackSafe : fixtureStackSafe comparisonNativeCode = true := by
  unfold fixtureStackSafe comparisonNativeCode
  rw [comparison_optimized_table,riscvNative_two_entry_code]
  with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The branching-loop witness is FFI-free and has no shared-memory operation. -/
theorem branching_stackSafe : fixtureStackSafe branchingLoopNativeCode = true := by
  unfold fixtureStackSafe branchingLoopNativeCode
  rw [branch_optimized_table,riscvNative_two_entry_code]
  with_unfolding_all decide


set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The original countdown compiler produces valid Lab code for every input. -/
theorem countdown_labGoodCode (n : Nat) (cfg : LabToTarget.Config) :
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode n) cfg).code) := by
  have sourceGood : pancakeGoodCodeHOL (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
      (progToHOL (countdown n))) = true := by
    simpa [countdown,progToHOL,expToHOL,shapeToHOL,countdownBody] using
      countdown_pancakeGoodCode (Flapjack.Basis.Pure.MlString.ofString "x") (BitVec.ofNat 64 n) 0
  have h := singleEntry_labGoodCode (progToHOL (countdown n)) (countdownWordPrograms n) (countdown_panToWord n) sourceGood
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The original comparison compiler produces valid Lab code. -/
theorem comparison_labGoodCode (cfg : LabToTarget.Config) :
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab comparisonNativeCode cfg).code) := by
  have sourceGood : pancakeGoodCodeHOL (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
      (progToHOL branching)) = true := by with_unfolding_all decide
  exact singleEntry_labGoodCode (progToHOL branching) comparisonWordPrograms comparison_panToWord sourceGood

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The original branching-loop compiler produces valid Lab code. -/
theorem branching_labGoodCode (cfg : LabToTarget.Config) :
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab branchingLoopNativeCode cfg).code) := by
  have sourceGood : pancakeGoodCodeHOL (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
      (progToHOL branchingLoop)) = true := by with_unfolding_all decide
  exact singleEntry_labGoodCode (progToHOL branchingLoop) branchWordPrograms branchingLoop_panToWord sourceGood

end SteppedFlapjack.Concrete
