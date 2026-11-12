import SteppedFlapjack.Concrete.NestedCodeFacts
open Flapjack Flapjack.Compiler.Backend SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Concrete
open Flapjack.RegAlloc Flapjack.RiscV.CakeRegAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.WordDepth
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.StackSteps Flapjack.Compiler.Backend.WordDepth.Executable
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics Flapjack.Compiler.Backend.StackRemove

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nested_costFactorTwo (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf nestedCode)) [4,2] (fixtureStackOracle cfg) = 2919 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  unfold nestedCode nestedNative
  rw [nested_optimizedTable, nestedRow0_exact, nestedRow1_exact, nestedRow2_exact, nestedRow3_exact]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nested_costFactorOne (cfg : LabToTarget.Config) :
    costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf nestedCode)) [4] (fixtureStackOracle cfg) = 1950 := by
  simp only [costFromFields,oracleBitmapBudget,Nat.add_zero,List.range_zero,List.flatMap_nil,maxListNat]
  unfold nestedCode nestedNative
  rw [nested_optimizedTable, nestedRow0_exact, nestedRow1_exact, nestedRow2_exact, nestedRow3_exact]
  decide +kernel

set_option maxHeartbeats 3000000 in
theorem nested_callDepth : Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth
    nestedFrameSizes 64 (sptFromAList nestedOptimizedWords) = some 5 := by
  rw [nested_frames, nested_optimizedTable, nestedRow0_exact, nestedRow1_exact, nestedRow2_exact, nestedRow3_exact]
  simp [Flapjack.Compiler.Backend.WordDepth.Executable.fullCallGraphDepth,
    Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptLookup_sptFromAList, sptAListLookup]
  split <;> simp_all [sptLookup_sptFromAList, sptAListLookup]
  all_goals obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›
  all_goals simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth,
    sptSize, sptFromAList, sptInsert]
  all_goals split <;> simp_all [sptLookup]
  all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
  all_goals simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth, sptDelete]
  all_goals split <;> simp_all [sptLookup, sptMkBN]
  all_goals try (obtain ⟨rfl,rfl⟩ := ‹_ ∧ _›)
  all_goals try simp [Flapjack.Compiler.Backend.WordDepth.Executable.callGraphDepth]
  all_goals with_unfolding_all rfl

theorem nested_capacity : optionLe
    (optionMap₂ max (some (max 1 (1+nestedEntryFrame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth nestedFrameSizes 64 (sptFromAList nestedOptimizedWords))))
    (some 2097172) := by
  rw [nested_entryFrame, nested_callDepth]
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem nested_compilerFacts : (fixtureRemoveLabels nestedCode).isSome = true ∧
    (fixtureCodeBytes nestedCode).length ≤ 0xecc ∧ (fixtureCodeBytes nestedCode).length % 4 = 0 := by
  constructor
  · unfold fixtureRemoveLabels nestedCode nestedNative
    rw [nested_optimizedTable, nestedRow0_exact, nestedRow1_exact, nestedRow2_exact, nestedRow3_exact]
    with_unfolding_all decide
  · unfold fixtureCodeBytes nestedCode nestedNative
    rw [nested_optimizedTable, nestedRow0_exact, nestedRow1_exact, nestedRow2_exact, nestedRow3_exact]
    simp_rw [LabToTarget.progToBytesMap]
    with_unfolding_all decide

open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
theorem nested_wordWeightValue : wordCodeWeight (sptFromAList nestedOptimizedWords) = 13 := by
  rw [nested_optimizedTable, nestedRow0_exact,
    nestedRow1_exact,
    nestedRow2_exact,
    nestedRow3_exact]
  with_unfolding_all decide
theorem nested_stackWeightValue : stackCodeWeight (sptFromAList nestedCode) = 57 := by
  unfold nestedCode nestedNative
  rw [nested_optimizedTable, nestedRow0_exact,
    nestedRow1_exact,
    nestedRow2_exact,
    nestedRow3_exact]
  with_unfolding_all decide


end SteppedFlapjack.Concrete
