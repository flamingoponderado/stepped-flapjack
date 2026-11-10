import SteppedFlapjack.Concrete.CountdownOptimized
import SteppedFlapjack.PanToCrepSteps.CountdownColoring
import SteppedFlapjack.StackRemoveSteps.InitStackNonempty
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.WordToWord SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

namespace SteppedFlapjack.Concrete

/-- The optimized countdown loop for an arbitrary initial count. -/
noncomputable def countdownOptimizedLoop (n : Nat) : WordLangProgHOL (BitVec 64) :=
  ((countdownOptimizedLiteral (BitVec.ofNat 64 n)).get ⟨1,by simp [countdownOptimizedLiteral]⟩).2.2

/-- Word state produced by the native initializer with the actual optimized table. -/
noncomputable def countdownInitialWord {C F : Type} (n : Nat) (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    WordSemStateFiniteExact 64 (Nat × C) F :=
  WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
    (WordToStack.Native.Initialization.makeInit riscvConfig countdownZeroLimit stack
      (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2) coracle)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The optimized countdown loop contains no calls. -/
theorem countdownOptimizedLoop_shape (n : Nat) : LoopSequence (countdownOptimizedLoop n) := by
  unfold countdownOptimizedLoop countdownOptimizedLiteral
  repeat (first | apply LoopSequence.seq | apply LoopSequence.loop | apply LoopSequence.branch |
    apply Branch.seq | apply Branch.ite | constructor)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The optimized table contains the countdown loop. -/
theorem countdownOptimizedLoop_lookup (n : Nat) : sptLookup 65 (sptFromAList
  (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2) = some (1,countdownOptimizedLoop n) := by
  rw [countdown_optimized_literal, sptLookup_sptFromAList]
  simp [sptAListLookup, countdownOptimizedLoop, countdownOptimizedLiteral]

/-- The optimized entry wrapper tail-calls the countdown loop. -/
def countdownOptimizedEntry : WordLangProgHOL (BitVec 64) :=
  .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none)

/-- The entry function in the original two-function Word table. -/
noncomputable def countdownSourceWordEntry (n : Nat) : WordLangProgHOL (BitVec 64) :=
  ((countdownWordLiteral (BitVec.ofNat 64 n) 0).get ⟨0,by simp [countdownWordLiteral]⟩).2.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The compiler-selected entry is the actual optimized tail wrapper. -/
theorem countdown_compilerSelectedEntry (n : Nat) :
  (fullCompileSingle riscvConfig.twoRegArith (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    countdownRiscVBackend.wordToWordConf.regAlg riscvConfig
      ((64,1,countdownSourceWordEntry n),entryColour countdownRiscVBackend.wordToWordConf (countdownWordPrograms n) 64)).2.2 = countdownOptimizedEntry := by
  have member : (64,1,countdownSourceWordEntry n) ∈ countdownWordPrograms n := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral,countdownSourceWordEntry]
  have nodup : ((countdownWordPrograms n).map Prod.fst).Nodup := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral]
  have h := (wholeCompile_entry_lookups countdownRiscVBackend.wordToWordConf riscvConfig
    (countdownWordPrograms n) 64 1 (countdownSourceWordEntry n) member nodup).2
  rw [countdown_optimized_literal, sptLookup_sptFromAList] at h
  simpa [sptAListLookup,countdownOptimizedLiteral,countdownOptimizedEntry] using h.symm

/-- Every countdown compiler-selected entry requires zero Stack frame space. -/
theorem countdown_compilerEntryFrame_zero (n : Nat) :
  nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    (fullCompileSingle riscvConfig.twoRegArith (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
      countdownRiscVBackend.wordToWordConf.regAlg riscvConfig
        ((64,1,countdownSourceWordEntry n),entryColour countdownRiscVBackend.wordToWordConf (countdownWordPrograms n) 64)).2.2 = 0 := by
  rw [countdown_compilerSelectedEntry]
  with_unfolding_all rfl

end SteppedFlapjack.Concrete
