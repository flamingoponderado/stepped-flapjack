import SteppedFlapjack.Concrete.CountdownStackSafety
import SteppedFlapjack.Concrete.WordBitmap
import SteppedFlapjack.WordToStackSteps.NativeEntrySpan
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.Concrete

/-- The optimized entry is a supported direct tail call. -/
theorem countdownEntry_shape : RegTailShape countdownOptimizedEntry := by
  apply RegTailShape.seq
  · apply RegTailShape.branch; exact Branch.move 1 [(0,0)]
  · exact RegTailShape.call 65 0

theorem countdownEntry_noInstall : noInstallSubprogsHOL countdownOptimizedEntry = true := by rfl

theorem countdownEntry_flat : flatExpConventions countdownOptimizedEntry = true := by rfl

theorem countdownEntry_convention : postAllocConventionsHOL (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = true := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem countdownCallee_flat (n : Nat) : flatExpConventions (countdownOptimizedLoop n) = true := by
  simp [countdownOptimizedLoop,countdownOptimizedLiteral,flatExpConventions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem countdownTable_noInstall (n : Nat) : WordProps.noInstallCode
    (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2) := by
  intro key arity program lookup
  rw [countdown_optimized_literal,sptLookup_sptFromAList] at lookup
  have member := sptAListLookup_mem key (countdownOptimizedLiteral (BitVec.ofNat 64 n)) (arity,program) lookup
  simp only [countdownOptimizedLiteral,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with first | second
  · cases first
    exact countdownEntry_noInstall
  · cases second
    exact loopSequence_noInstall (countdownOptimizedLoop_shape n)

theorem countdownEntry_localCode (n : Nat) : RegTailLocalCode countdownOptimizedEntry
    (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2) := by
  intro loc call
  cases call with
  | left h => cases h
  | right h =>
    cases h
    exact ⟨1,countdownOptimizedLoop n,countdownOptimizedLoop_lookup n,
      flat_loopSequence_block (countdownOptimizedLoop_shape n) (countdownCallee_flat n)⟩
theorem countdownNativeEntryWord_eq {C F : Type} (n clock : Nat) (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    nativeTailEntryWord countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64
      (countdownSourceWordEntry n) stack coracle clock = {(countdownInitialWord n stack coracle) with clock := clock} := by
  simp only [nativeTailEntryWord,nativeTailEntryCode,countdown_compilerEntryFrame_zero,countdownInitialWord]
  rfl
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization

/-- The initialized native countdown entry has an exact Stack result and a code-derived visit bound. -/
theorem countdown_stack_span {C F : Type} (n clock limit : Nat)
    (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2)
    (bitmaps : (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).1.IsPrefix stack.bitmaps)
    (ok : initStateOk riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) stack coracle)
    (nonempty : 1 ≤ stack.stack.length) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × C) F)
    (run : evaluate countdownOptimizedEntry {(countdownInitialWord n stack coracle) with clock := clock} = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (complete : CompleteWordResult result)
    (bound : SteppedFlapjack.WordSteps.steps countdownOptimizedEntry
      {(countdownInitialWord n stack coracle) with clock := clock} ≤ limit) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl 64) none,{stack with clock := limit+1}) = (targetResult,targetPost) ∧
      result.map compileResult = targetResult ∧ post.ffi = targetPost.ffi ∧
      SteppedFlapjack.StackSteps.steps (.call none (.inl 64) none,{stack with clock := limit+1}) ≤
        nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) limit := by
  have member : (64,1,countdownSourceWordEntry n) ∈ countdownWordPrograms n := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral,countdownSourceWordEntry]
  have nodup : ((countdownWordPrograms n).map Prod.fst).Nodup := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral]
  have noRaise : raiseStubLocation ∉ (countdownWordPrograms n).map Prod.fst := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral,raiseStubLocation,wordNumStubs,stackNumStubs]
  have noStore : storeConstsStubLocation ∉ (countdownWordPrograms n).map Prod.fst := by
    rw [countdownWordPrograms_literal]
    simp [countdownWordLiteral,storeConstsStubLocation,wordNumStubs,stackNumStubs]
  have selected : nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) = countdownOptimizedEntry := countdown_compilerSelectedEntry n
  have fits : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
      (nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n)) ≤ stack.stackSpace := by
    change nativeEntryFrameSize _ (fullCompileSingle riscvConfig.twoRegArith _ _ riscvConfig ((64,1,countdownSourceWordEntry n),entryColour _ _ 64)).2.2 ≤ _
    rw [countdown_compilerEntryFrame_zero]
    omega
  have safe0 := countdown_entry_resource_safe n stack coracle (countdownInitialWord n stack coracle).locals clock nonempty
  have safe : post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
    change (evaluate countdownOptimizedEntry {(countdownInitialWord n stack coracle) with clock := clock}).2.stackMax.getD ((evaluate countdownOptimizedEntry {(countdownInitialWord n stack coracle) with clock := clock}).2.stackLimit+1) ≤ (evaluate countdownOptimizedEntry {(countdownInitialWord n stack coracle) with clock := clock}).2.stackLimit at safe0
    rw [run] at safe0
    exact safe0
  apply nativeTailEntry_span countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64
    (countdownSourceWordEntry n) member nodup stack coracle noRaise noStore codeEq bitmaps ok fits clock limit result post
  · rw [selected]; exact countdownEntry_shape
  · rw [selected]; exact countdownEntry_noInstall
  · rw [countdownNativeEntryWord_eq]
    change WordProps.noInstallCode (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2)
    exact countdownTable_noInstall n
  · rw [selected,countdownNativeEntryWord_eq]
    change RegTailLocalCode countdownOptimizedEntry (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2)
    exact countdownEntry_localCode n
  · rw [selected]; exact countdownEntry_convention
  · rw [selected]; exact countdownEntry_flat
  · rw [selected,countdownNativeEntryWord_eq]; exact run
  · exact notError
  · exact notTimeout
  · exact complete
  · exact safe
  · rw [selected,countdownNativeEntryWord_eq]; exact bound

/-- The countdown compiler emits only the standard single bitmap word. -/
theorem countdown_native_bitmaps (n : Nat) :
 (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).1 = [4] := by
  unfold countdownWordPrograms countdownCrepCode
  rw [← twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (naturalCountdown_scalar n)]
  exact twoWordTables_native_bitmaps riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n))) (naturalCountdown_scalar n)
    countdownRiscVBackend.wordToWordConf riscvConfig

end SteppedFlapjack.Concrete
