import SteppedFlapjack.Concrete.CountdownAllocationLiteral
import SteppedFlapjack.Concrete.NaturalCountdownWordSpan
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

set_option maxHeartbeats 1000000 in
private theorem countdownBoundCoefficient (n limit : Nat) :
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) limit phase3WordConfig riscvConfig = 1 + 99*(6*limit+2) := by
  have h := countdownExecutableTable (BitVec.ofNat 64 n)
  unfold twoProgramWordBound
  rw [countdownTwoLoops_literal, countdownCallee_literal, countdownLoopLiteral_toWord, countdownCalleeWord_literal]
  dsimp [compileWith,phase3WordConfig,countdownWordLiteral,nextNOracle,countdownOptimizedLiteral] at h
  simp only [List.map_cons,List.map_nil,List.cons.injEq,and_true] at h
  have he := congrArg (fun row : Nat × Nat × WordLangProgHOL (BitVec 64) => SteppedFlapjack.WordSimpSteps.wordControlWeight row.2.2) h.1
  have hc := congrArg (fun row : Nat × Nat × WordLangProgHOL (BitVec 64) => SteppedFlapjack.WordSimpSteps.wordControlWeight row.2.2) h.2
  simp only [SteppedFlapjack.WordSimpSteps.wordControlWeight] at he hc
  have e64 : entryColour phase3WordConfig (countdownWordLiteral (BitVec.ofNat 64 n) 0) 64 = none := by rfl
  have e65 : entryColour phase3WordConfig (countdownWordLiteral (BitVec.ofNat 64 n) 0) 65 = none := by rfl
  dsimp only
  rw [e64,e65]
  have ew : loopToWordCompFuncHOL 64 [] branchingLoopEntry =
      ((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨0, by simp [countdownWordLiteral]⟩).2.2 := by
    with_unfolding_all rfl
  rw [ew]
  change 1 + SteppedFlapjack.WordSimpSteps.wordControlWeight
      (fullCompileSingleWith RegAlloc.regAllocExecutable riscvConfig.twoRegArith
        (riscvConfig.regCount - (5+riscvConfig.avoidRegs.length)) 3 riscvConfig
        (((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨0,by simp [countdownWordLiteral]⟩),none)).2.2 *
      (SteppedFlapjack.WordSimpSteps.wordControlWeight
      (fullCompileSingleWith RegAlloc.regAllocExecutable riscvConfig.twoRegArith
        (riscvConfig.regCount - (5+riscvConfig.avoidRegs.length)) 3 riscvConfig
        (((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨1,by simp [countdownWordLiteral]⟩),none)).2.2 + 1) *
      (6*limit+2) = _
  have he' : SteppedFlapjack.WordSimpSteps.wordControlWeight
      (fullCompileSingleWith RegAlloc.regAllocExecutable riscvConfig.twoRegArith
        (riscvConfig.regCount - (5+riscvConfig.avoidRegs.length)) 3 riscvConfig
        (((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨0,by simp [countdownWordLiteral]⟩),none)).2.2 = 3 := by
    simpa [countdownWordLiteral] using he
  have hc' : SteppedFlapjack.WordSimpSteps.wordControlWeight
      (fullCompileSingleWith RegAlloc.regAllocExecutable riscvConfig.twoRegArith
        (riscvConfig.regCount - (5+riscvConfig.avoidRegs.length)) 3 riscvConfig
        (((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨1,by simp [countdownWordLiteral]⟩),none)).2.2 = 32 := by
    simpa [countdownWordLiteral] using hc
  rw [he',hc']

/-- Closed-form Word visit limit for the original countdown fixture. -/
theorem countdown_bound_closed (n : Nat) : countdownWordBound n = 232771968*n+717718519 := by
  unfold countdownWordBound
  rw [countdownBoundCoefficient]
  unfold countdownLoopVisits countdownLoopBudget
  omega

/-- Closed-form Word visit limit for the unprefixed countdown fixture. -/
theorem naturalCountdown_bound_closed (n : Nat) : naturalCountdownWordBound n = 232771968*n+640127863 := by
  unfold naturalCountdownWordBound
  rw [countdownBoundCoefficient]
  unfold naturalCountdownLoopVisits naturalCountdownLoopBudget
  omega

end SteppedFlapjack.Concrete
