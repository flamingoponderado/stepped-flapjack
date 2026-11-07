import SteppedFlapjack.PanToCrepSteps.CountdownZeroFrames
import SteppedFlapjack.WordSimpSteps.ZeroFrameTail
import SteppedFlapjack.StackRemoveSteps.InitStackNonempty

/-! The compiled countdown loop cannot increase the Word stack maximum. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSimpSteps

/-- The actual allocated and cleaned countdown loop body. -/
def countdownZeroOptimizedLoop : WordLangProgHOL (BitVec 64) :=
  WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour countdownZeroColor) countdownZeroAllocInput)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The actual optimized loop has no calls, including inside its loop body. -/
theorem countdownZeroOptimizedLoop_shape : LoopSequence countdownZeroOptimizedLoop := by
  unfold countdownZeroOptimizedLoop
  with_unfolding_all
    repeat (first | apply LoopSequence.seq | apply LoopSequence.loop | apply LoopSequence.branch |
      apply Branch.seq | apply Branch.ite | constructor)

/-- Executing the actual optimized loop leaves the recorded stack maximum
unchanged, for every initial Word state and every result. -/
theorem countdownZeroOptimizedLoop_stackMax {C F : Type} (s : WordSemStateFiniteExact 64 C F) :
    (WordSemStateFiniteExact.evaluate countdownZeroOptimizedLoop s).2.stackMax = s.stackMax :=
  loopSequence_stackMax countdownZeroOptimizedLoop_shape s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The Word compiler code table resolves location 65 to that exact loop. -/
theorem countdownZeroOptimizedLoop_lookup :
    sptLookup 65 (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa
        (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
          (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))))).2) = some (1,countdownZeroOptimizedLoop) := by
  rw [← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The Word initializer assigns the concrete loop a zero-sized frame. -/
theorem countdownZeroOptimizedLoop_frame_lookup :
    sptLookup 65 (sptMapi (fun _ (arity,prog) =>
      (WordToStack.Native.compileProgNative riscvConfig false prog arity countdownZeroLimit (.nil,0)).2.1)
      (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa
          (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2)) = some 0 := by
  rw [← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all rfl

/-- Actual optimized Word code table for the zero-count example. -/
noncomputable def countdownZeroWordCode : Spt (Nat × WordLangProgHOL (BitVec 64)) :=
  sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
    (panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))))).2

/-- Word state created by the native initializer and zero-sized entry frame. -/
noncomputable def countdownZeroInitialWord {C F : Type} (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    WordSemStateFiniteExact 64 (Nat × C) F :=
  WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
    (WordToStack.Native.Initialization.makeInit riscvConfig countdownZeroLimit stack countdownZeroWordCode coracle)

/-- Starting from the actual Word initializer, the call to the countdown
loop returns with recorded stack maximum one, regardless of the state or
result of the loop. -/
theorem countdownZero_directTail_stackMax {C F : Type} (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    (WordSemStateFiniteExact.evaluate (.call none (some 65) [0] none)
      (countdownZeroInitialWord stack coracle)).2.stackMax = some 1 := by
  apply directTail_zeroFrame_stackMax 65 countdownZeroOptimizedLoop countdownZeroOptimizedLoop_shape
  · change sptLookup 65 countdownZeroWordCode = _
    exact countdownZeroOptimizedLoop_lookup
  · change sptLookup 65 (sptMapi (fun _ (arity,prog) =>
      (WordToStack.Native.compileProgNative riscvConfig false prog arity countdownZeroLimit (.nil,0)).2.1)
      countdownZeroWordCode) = _
    exact countdownZeroOptimizedLoop_frame_lookup
  · rfl
  · rfl

/-- The optimized entry moves its return location and tail-calls the loop. -/
def countdownZeroOptimizedEntry : WordLangProgHOL (BitVec 64) :=
  .seq (.move 1 [(0,0)]) (.call none (some 65) [0] none)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The actual compiled Word code table contains the exact entry wrapper. -/
theorem countdownZeroOptimizedEntry_lookup :
    sptLookup 64 countdownZeroWordCode = some (1,countdownZeroOptimizedEntry) := by
  unfold countdownZeroWordCode
  rw [← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all rfl

/-- The actual Word entry wrapper preserves the one-word stack maximum,
including when its locals or clock are replaced by the simulation setup. -/
theorem countdownZero_entryWord_stackMax {C F : Type} (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) :
    (WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock}).2.stackMax = some 1 := by
  apply moveTail_zeroFrame_stackMax 65 countdownZeroOptimizedLoop countdownZeroOptimizedLoop_shape
  · change sptLookup 65 countdownZeroWordCode = _
    exact countdownZeroOptimizedLoop_lookup
  · change sptLookup 65 (sptMapi (fun _ (arity,prog) =>
      (WordToStack.Native.compileProgNative riscvConfig false prog arity countdownZeroLimit (.nil,0)).2.1)
      countdownZeroWordCode) = _
    exact countdownZeroOptimizedLoop_frame_lookup
  · rfl
  · rfl

/-- A run of the concrete optimized entry keeps stack maximum one and keeps
the initialized stack limit. -/
theorem countdownZero_entryWord_stack_usage {C F : Type} (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × C) F)
    (run : WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock} = (result,post)) :
    post.stackMax = some 1 ∧ post.stackLimit = stack.stack.length := by
  constructor
  · have maximum := countdownZero_entryWord_stackMax stack coracle locals clock
    rw [run] at maximum
    exact maximum
  · have limit := WordSemStateFiniteExact.evaluate_stack_limit countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock} result post run
    simpa [countdownZeroInitialWord,WordSemStateFiniteExact.callEnv,
      WordToStack.Native.Initialization.makeInit] using limit

/-- A nonempty initialized stack excludes the later Word-to-Stack resource
condition for this actual entry run. -/
theorem countdownZero_entryWord_no_resource {C F : Type} (stack : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × C) F)
    (run : WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock} = (result,post))
    (nonempty : 1 ≤ stack.stack.length) :
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  obtain ⟨maximum,limit⟩ := countdownZero_entryWord_stack_usage stack coracle locals clock result post run
  simp only [maximum,Option.getD_some,limit]
  exact nonempty

/-- For every actual full-initializer context, the concrete Word entry run
cannot satisfy the Word-to-Stack resource condition. -/
theorem countdownZero_fullInit_entry_no_resource {F : Type}
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (backend : SteppedFlapjack.LoopToWordSteps.FullInitMachineContext stack)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (run : WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock} = (result,post)) :
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  apply countdownZero_entryWord_no_resource stack coracle locals clock result post run
  rw [backend.stackEq]
  exact SteppedFlapjack.StackRemoveSteps.fullMakeInit_stack_nonempty _ _ _ _ _ _ _ _ _ _ _

/-- The actual initialized Word entry execution stays within its stack limit,
without a supplied execution or stack-size premise. -/
theorem countdownZero_fullInit_entry_resource_safe {F : Type}
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (backend : SteppedFlapjack.LoopToWordSteps.FullInitMachineContext stack)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (locals : Spt (WordLocW 64)) (clock : Nat) :
    let post := (WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
      {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock}).2
    post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit := by
  let run := WordSemStateFiniteExact.evaluate countdownZeroOptimizedEntry
    {(countdownZeroInitialWord stack coracle) with locals := locals, clock := clock}
  exact countdownZero_fullInit_entry_no_resource stack backend coracle locals clock run.1 run.2 (by change run = (run.1,run.2); cases run; rfl)

end SteppedFlapjack.PanToCrepSteps
