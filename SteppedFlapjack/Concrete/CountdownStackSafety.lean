import SteppedFlapjack.Concrete.CountdownStackFrames
import SteppedFlapjack.WordSimpSteps.ZeroFrameTail
import SteppedFlapjack.StackRemoveSteps.InitStackNonempty
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The native initializer assigns the loop a zero-sized frame. -/
theorem countdownOptimizedLoop_frame_lookup (n : Nat) : sptLookup 65 (sptMapi (fun _ (arity,prog) =>
      (WordToStack.Native.compileProgNative riscvConfig false prog arity countdownZeroLimit (.nil,0)).2.1)
      (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2)) = some 0 := by
  rw [countdown_optimized_literal, sptLookupMapi, sptLookup_sptFromAList]
  simp [countdownOptimizedLiteral, sptAListLookup, WordToStack.Native.compileProgNative, maxVarHOL, countdownZeroLimit, maxVarInstHOL]
  constructor <;> with_unfolding_all rfl

/-- The optimized entry wrapper tail-calls the countdown loop. -/
def countdownOptimizedEntry : WordLangProgHOL (BitVec 64) :=
  .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none)

/-- The entry run records a stack maximum of exactly one for every count. -/
theorem countdown_entry_stackMax {C F : Type} (n : Nat) (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) :
    (WordSemStateFiniteExact.evaluate countdownOptimizedEntry
      {(countdownInitialWord n stack coracle) with locals := locals, clock := clock}).2.stackMax = some 1 := by
  apply moveTail_zeroFrame_stackMax 65 (countdownOptimizedLoop n) (countdownOptimizedLoop_shape n)
  · exact countdownOptimizedLoop_lookup n
  · exact countdownOptimizedLoop_frame_lookup n
  · rfl
  · rfl

/-- A nonempty stack excludes the Word-to-Stack resource condition. -/
theorem countdown_entry_resource_safe {C F : Type} (n : Nat) (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat)
    (nonempty : 1 ≤ stack.stack.length) :
    let post := (WordSemStateFiniteExact.evaluate countdownOptimizedEntry
      {(countdownInitialWord n stack coracle) with locals := locals, clock := clock}).2
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  let s := {(countdownInitialWord n stack coracle) with locals := locals, clock := clock}
  rcases run : WordSemStateFiniteExact.evaluate countdownOptimizedEntry s with ⟨res,post⟩
  have maximum := countdown_entry_stackMax n stack coracle locals clock
  change (WordSemStateFiniteExact.evaluate countdownOptimizedEntry s).2.stackMax = some 1 at maximum
  rw [run] at maximum
  change post.stackMax = some 1 at maximum
  have limit := WordSemStateFiniteExact.evaluate_stack_limit countdownOptimizedEntry s res post run
  change post.stackLimit = stack.stack.length at limit
  change post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit
  simp only [maximum,Option.getD_some,limit]
  exact nonempty

end SteppedFlapjack.Concrete
