import SteppedFlapjack.Concrete.CountdownAllocationLiteral
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.RegAlloc Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.WordAllocSteps
namespace SteppedFlapjack.Concrete

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem countdownOptimizedCallee (x : BitVec 64) :
 fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
   ((65,1,countdownWordCallee x),none) = (65,1,((countdownOptimizedLiteral x).get ⟨1,by simp [countdownOptimizedLiteral]⟩).2.2) := by
  simp only [fullCompileSingleWith,compileSingleWith,countdown_wordSimp_literal,countdown_instruction_literal,
    countdown_ssa_literal,countdown_firstDead_literal,countdown_cse_literal,countdown_copy_literal,countdown_twoReg_literal,
    countdown_unreach_literal,countdown_secondDead_literal,countdown_wordAlloc_literal,countdown_apply_color_literal]

private theorem countdownOptimizedEntry (x : BitVec 64) :
 fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
   ((64,1,((countdownWordLiteral x 0).get ⟨0,by simp [countdownWordLiteral]⟩).2.2),none) =
   ((countdownOptimizedLiteral x).get ⟨0,by simp [countdownOptimizedLiteral]⟩) := by
  simpa [countdownWordLiteral,countdownOptimizedLiteral] using countdown_entry_optimized

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem countdownExecutableTable (x : BitVec 64) :
 (compileWith regAllocExecutable phase3WordConfig riscvConfig (countdownWordLiteral x 0)).2 = countdownOptimizedLiteral x := by
  have h := countdownOptimizedCallee x
  have e := countdownOptimizedEntry x
  dsimp [compileWith,phase3WordConfig,nextNOracle,countdownWordLiteral] at ⊢
  change [_,fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
    ((65,1,countdownWordCallee x),none)] = _
  rw [h]
  exact congrArg (fun t => [t,(65,1,((countdownOptimizedLiteral x).get ⟨1,by simp [countdownOptimizedLiteral]⟩).2.2)]) e

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
/-- The actual optimized RISC-V Word table, including allocation, for every count. -/
theorem countdown_optimized_literal (n : Nat) :
 (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2 =
    countdownOptimizedLiteral (BitVec.ofNat 64 n) := by
  have allocator : regAllocExecutable = regAlloc := by
    funext a b c d e f g
    exact regAllocExecutable_eq a b c d e f g
  rw [← phase3WordConfig_eq, countdownWordPrograms_literal,
    ← compileWith_eq_compile _ allocator]
  exact countdownExecutableTable (BitVec.ofNat 64 n)

end SteppedFlapjack.Concrete
