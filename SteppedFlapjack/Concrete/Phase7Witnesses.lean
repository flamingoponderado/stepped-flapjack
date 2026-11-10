import SteppedFlapjack.Concrete.Phase7Machine
import SteppedFlapjack.Concrete.FixtureMachineResults
import SteppedFlapjack.Concrete.BranchingFrames
import SteppedFlapjack.Concrete.FixedWordBounds
import SteppedFlapjack.Concrete.CountdownLabBounds
import SteppedFlapjack.Concrete.WitnessWeights

/-! Concrete instances of the supported source-to-machine theorem. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordToStackSteps

private theorem comparison_callee : supportedCallee branchingHOL = branchCrepBody := by
  have h := supported_crepPrograms branching branching_supported
  rw [← branching_hol_eq,branching_crep_code] at h
  simpa [twoPrograms,branchCrepBody] using h.symm

private theorem comparison_words : supportedWordPrograms branching = comparisonWordPrograms := by
  unfold supportedWordPrograms
  rw [branching_simp_program,← branching_hol_eq,branching_crep_code]
  rfl

private theorem comparison_native : (supportedNative branching).2.2.2 = comparisonNativeCode := by
  simp only [supportedNative,supportedAllocated_eq,comparison_words,comparisonNativeCode]

private theorem comparison_frame : supportedCalleeFrame branching ≤
    (fixtureStack (supportedNative branching).2.2.2 (fixtureCompilerConfig (supportedNative branching).2.2.2)).stack.length := by
  let cfg := fixtureCompilerConfig (supportedNative branching).2.2.2
  have frame := comparison_fixture_callee_frame cfg
  change sptLookup 65 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2)) = some 0 at frame
  rw [sptLookupMapi] at frame
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,comparison_words]
  cases found : sptLookup 65 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2) with
  | none => simp [found] at frame
  | some pair =>
    obtain ⟨arity,callee⟩ := pair
    simp only [found,Option.map_some,Option.some.injEq] at frame
    dsimp only
    rw [frame]
    exact fixtureStack_nonempty _ _

private theorem comparison_crepBudget : supportedCrepBudget branching 6 = 33 := by
  simp [supportedCrepBudget,branching_simp_program,← branching_hol_eq,comparison_callee,branchCrepBody,CrepSteps.statementWeight]

private theorem comparison_loopBudget : supportedLoopBudget branching 6 = comparisonLoopBudget := by
  unfold supportedLoopBudget comparisonLoopBudget
  rw [branching_simp_program,← branching_hol_eq]
  dsimp only
  rw [comparison_callee,comparison_optimized_weight,comparison_crepBudget]

private theorem comparison_loopVisits : supportedLoopVisits branching 6 = comparisonLoopVisits := by
  unfold supportedLoopVisits comparisonLoopVisits
  rw [branching_simp_program,← branching_hol_eq]
  dsimp only
  rw [comparison_callee,comparison_optimized_weight,comparison_crepBudget,comparison_loopBudget]

private theorem comparison_wordBound : supportedWordBound branching 6 = comparisonWordBound := by
  unfold supportedWordBound comparisonWordBound
  rw [branching_simp_program,← branching_hol_eq]
  dsimp only
  rw [comparison_callee,comparison_loopVisits]

private theorem comparison_stackBound : supportedStackBound branching 6 = 860921207 := by
  unfold supportedStackBound
  rw [comparison_words,comparison_wordBound]
  change nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms 64
    (loopToWordCompFuncHOL 64 [] branchingLoopEntry) comparisonWordBound = _
  rw [comparison_stackBound_closed,comparison_bound_closed]

private theorem comparison_ticks : supportedMachineFactor branching * 6 + supportedMachineOffset branching = 90715439766875148 := by
  rw [← supportedMachineTicks_affine]
  unfold supportedMachineTicks
  rw [comparison_native,comparison_stackBound]
  dsimp only
  rw [comparisonLabTick_closed]

private def witnessContext : PanValueFfiContext (RiscV.Word 64) := riscv64PanValueFfiContext (fun _ => false)
private def witnessPrimitive : PanPrimitiveHandler (RiscV.Word 64) := fun _ _ => none
private def witnessHandler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit := fun _ _ _ _ _ _ _ => none

/-- The comparison witness is an unconditional instance of the Phase 7 theorem. -/
theorem comparisonFixture_machine :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL branching)) = some (fixtureCodeBytes comparisonNativeCode,[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart comparisonNativeCode)) sourceFfi
      90715439766875148
      (fixtureMachineState comparisonNativeCode) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL branching)).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL branching)) = .terminate .success ffiPost.ioEvents := by
  have sourceRun := branching_run witnessContext witnessPrimitive witnessHandler
  have run : evalPanValueFfiProgSteps witnessContext witnessPrimitive witnessHandler (executableState (progToHOL branching)).structs []
      (executableState (progToHOL branching)).baseAddress (executableState (progToHOL branching)).topAddress
      panSemBitVec64BytesInWord 2 (executableState (progToHOL branching)).locals
      (executableState (progToHOL branching)).globals (executableState (progToHOL branching)).memory
      (executableState (progToHOL branching)).ffi branching
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL branching)))) =
        some (.returned (executableState (progToHOL branching)).locals (executableState (progToHOL branching)).globals
          (executableState (progToHOL branching)).memory (executableState (progToHOL branching)).ffi [.word 7],6) := by
    simpa only [← branching_hol_eq] using sourceRun
  have safe : fixtureStackSafe (supportedNative branching).2.2.2 = true := by
    rw [comparison_native]
    exact comparison_stackSafe
  have facts : (fixtureRemoveLabels (supportedNative branching).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative branching).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative branching).2.2.2).length % 4 = 0 := by
    rw [comparison_native]
    exact comparison_compiler_facts
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine branching branching_supported witnessContext witnessPrimitive witnessHandler 2 6 6
      _ _ _ _ 7 run (by omega) comparison_frame safe facts
  rw [comparison_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [comparison_native] using compiled,
    machinePost,ffiPost,by simpa only [comparison_native] using machineRun,events,semantics⟩

private theorem branch_callee : supportedCallee (progToHOL branchingLoop) = branchingLoopCrepBody := by
  have h := supported_crepPrograms branchingLoop branchingLoop_supported
  rw [branchingLoop_crep_code] at h
  simpa [twoPrograms] using h.symm

private theorem branch_words : supportedWordPrograms branchingLoop = branchWordPrograms := by
  unfold supportedWordPrograms
  rw [branchingLoop_simp_program,branchingLoop_crep_code]
  rfl

private theorem branch_native : (supportedNative branchingLoop).2.2.2 = branchingLoopNativeCode := by
  simp only [supportedNative,supportedAllocated_eq,branch_words,branchingLoopNativeCode]

private theorem branch_frame : supportedCalleeFrame branchingLoop ≤
    (fixtureStack (supportedNative branchingLoop).2.2.2 (fixtureCompilerConfig (supportedNative branchingLoop).2.2.2)).stack.length := by
  let cfg := fixtureCompilerConfig (supportedNative branchingLoop).2.2.2
  have frame := branch_fixture_callee_frame cfg
  change sptLookup 65 (sptMapi _ (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2)) = some 0 at frame
  rw [sptLookupMapi] at frame
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,branch_words]
  cases found : sptLookup 65 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2) with
  | none => simp [found] at frame
  | some pair =>
    obtain ⟨arity,callee⟩ := pair
    simp only [found,Option.map_some,Option.some.injEq] at frame
    dsimp only
    rw [frame]
    exact fixtureStack_nonempty _ _

private theorem branch_crepBudget : supportedCrepBudget branchingLoop 23 = 388 := by
  simp [supportedCrepBudget,branchingLoop_simp_program,branch_callee,branchingLoopCrepBody,CrepSteps.statementWeight]

private theorem branch_loopBudget : supportedLoopBudget branchingLoop 23 = branchLoopBudget := by
  unfold supportedLoopBudget branchLoopBudget
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,conditional_optimized_weight,branch_crepBudget]

private theorem branch_loopVisits : supportedLoopVisits branchingLoop 23 = branchLoopVisits := by
  unfold supportedLoopVisits branchLoopVisits
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,conditional_optimized_weight,branch_crepBudget,branch_loopBudget]

private theorem branch_wordBound : supportedWordBound branchingLoop 23 = branchWordBound := by
  unfold supportedWordBound branchWordBound
  rw [branchingLoop_simp_program]
  dsimp only
  rw [branch_callee,branch_loopVisits]

private theorem branch_stackBound : supportedStackBound branchingLoop 23 = 348971665463 := by
  unfold supportedStackBound
  rw [branch_words,branch_wordBound]
  change nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms 64
    (loopToWordCompFuncHOL 64 [] branchingLoopEntry) branchWordBound = _
  rw [branch_stackBound_closed,branch_bound_closed]

private theorem branch_ticks : supportedMachineFactor branchingLoop * 23 + supportedMachineOffset branchingLoop = 36771214184170446348 := by
  rw [← supportedMachineTicks_affine]
  unfold supportedMachineTicks
  rw [branch_native,branch_stackBound]
  dsimp only
  rw [branchingLoopLabTick_closed]

/-- The branching-loop witness is an unconditional instance of the Phase 7 theorem. -/
theorem branchingLoopFixture_machine :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL branchingLoop)) = some (fixtureCodeBytes branchingLoopNativeCode,[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart branchingLoopNativeCode)) sourceFfi
      36771214184170446348 (fixtureMachineState branchingLoopNativeCode) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL branchingLoop)).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL branchingLoop)) = .terminate .success ffiPost.ioEvents := by
  have run := branchingLoop_source_run witnessContext witnessPrimitive witnessHandler
  have safe : fixtureStackSafe (supportedNative branchingLoop).2.2.2 = true := by
    rw [branch_native]
    exact branching_stackSafe
  have facts : (fixtureRemoveLabels (supportedNative branchingLoop).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative branchingLoop).2.2.2).length % 4 = 0 := by
    rw [branch_native]
    exact branching_compiler_facts
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine branchingLoop branchingLoop_supported witnessContext witnessPrimitive witnessHandler 7 23 23
      _ _ _ _ 7 run (by omega) branch_frame safe facts
  rw [branch_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [branch_native] using compiled,
    machinePost,ffiPost,by simpa only [branch_native] using machineRun,events,semantics⟩


private theorem natural_callee (n : Nat) : supportedCallee (naturalCountdownHOL n) = naturalCountdownCrepBody (BitVec.ofNat 64 n) := by
  have h := supported_crepPrograms (naturalCountdown n) (naturalCountdown_supported n)
  change crepPrograms (naturalCountdownHOL n) = _ at h
  rw [natural_countdown_crep_code] at h
  simpa [twoPrograms,naturalCountdownHOL] using h.symm

private theorem countdown_words (n : Nat) : supportedWordPrograms (countdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  rw [countdown_simp_program]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl

private theorem countdown_native (n : Nat) : (supportedNative (countdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,countdown_words,countdownNativeStackCode]

private theorem countdown_frame (n : Nat) : supportedCalleeFrame (countdown n) ≤
    (fixtureStack (supportedNative (countdown n)).2.2.2 (fixtureCompilerConfig (supportedNative (countdown n)).2.2.2)).stack.length := by
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,countdown_words,countdownOptimizedLoop_lookup]
  dsimp only
  rw [nativeEntryFrameSize_compile]
  change 1 + nativeEntryFrameSize countdownZeroLimit (countdownOptimizedLoop n) ≤ _
  rw [countdownCallee_entryFrame_zero]
  exact fixtureStack_nonempty _ _

private theorem countdown_crepBudget (n : Nat) : supportedCrepBudget (countdown n) (6*n+9) = 3+8*(6*n+18) := by
  unfold supportedCrepBudget
  rw [countdown_simp_program]
  change 3 + CrepSteps.statementWeight (supportedCallee (naturalCountdownHOL n)) *
    (6*n+9+1+CrepSteps.statementWeight (supportedCallee (naturalCountdownHOL n))) = _
  rw [natural_callee]
  simp [naturalCountdownCrepBody,CrepSteps.statementWeight]

private theorem countdown_loopBudget (n : Nat) : supportedLoopBudget (countdown n) (6*n+9) = countdownLoopBudget n := by
  unfold supportedLoopBudget countdownLoopBudget
  rw [countdown_simp_program]
  dsimp only
  change 3 * loopVisitWeight (optimiseHOL (compileHOLExact _ .ln (supportedCallee (naturalCountdownHOL n)))) * _ = _
  rw [natural_callee]
  have weight := countdown_optimized_weight riscvConfig.isa n
  change loopVisitWeight (optimiseHOL (compileHOLExact (ctxtFcExact
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).target
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).funcs [] []) .ln
    (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 at weight
  rw [weight,countdown_crepBudget]

private theorem countdown_loopVisits (n : Nat) : supportedLoopVisits (countdown n) (6*n+9) = countdownLoopVisits n := by
  unfold supportedLoopVisits countdownLoopVisits
  rw [countdown_simp_program]
  dsimp only
  change loopVisitWeight (optimiseHOL (compileHOLExact _ .ln (supportedCallee (naturalCountdownHOL n)))) * _ + 8 = _
  rw [natural_callee]
  have weight := countdown_optimized_weight riscvConfig.isa n
  change loopVisitWeight (optimiseHOL (compileHOLExact (ctxtFcExact
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).target
    (witnessLoopContext riscvConfig.isa (progToHOL (naturalCountdown n))).funcs [] []) .ln
    (naturalCountdownCrepBody (BitVec.ofNat 64 n)))) = 52 at weight
  rw [weight,countdown_crepBudget,countdown_loopBudget]

private theorem countdown_wordBound (n : Nat) : supportedWordBound (countdown n) (6*n+9) = countdownWordBound n := by
  unfold supportedWordBound countdownWordBound
  rw [countdown_simp_program]
  dsimp only
  change twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (supportedCallee (naturalCountdownHOL n)) (supportedLoopVisits (countdown n) (6*n+9)) phase3WordConfig riscvConfig = _
  rw [natural_callee,countdown_loopVisits]
  rfl

private theorem countdown_stackBound (n : Nat) : supportedStackBound (countdown n) (6*n+9) = 9543650688*n+29426459323 := by
  unfold supportedStackBound
  rw [countdown_words,countdown_wordBound]
  have entryEq : supportedEntry = countdownSourceWordEntry n := by with_unfolding_all rfl
  rw [entryEq]
  rw [countdown_stackBound_closed,countdown_bound_closed]
  omega

private theorem countdown_ticks (n : Nat) : supportedMachineFactor (countdown n) * (6*n+9) + supportedMachineOffset (countdown n) =
    167602730287449600*(6*n+9)+1592247331570371948 := by
  rw [← supportedMachineTicks_affine]
  unfold supportedMachineTicks
  rw [countdown_native,countdown_stackBound]
  dsimp only
  rw [countdownLabTick_closed]
  omega


/-- The prefixed countdown derives its original numerical bound from Phase 7. -/
theorem countdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL (countdown n))) = some (fixtureCodeBytes (countdownNativeStackCode n),[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600*(6*n+9)+1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL (countdown n))).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL (countdown n))) = .terminate .success ffiPost.ioEvents := by
  obtain ⟨result,_,sourceRun,_,_,resultEq⟩ := countdown_run n range witnessContext witnessPrimitive witnessHandler
  subst result
  have run : evalPanValueFfiProgSteps witnessContext witnessPrimitive witnessHandler (executableState (progToHOL (countdown n))).structs []
      (executableState (progToHOL (countdown n))).baseAddress (executableState (progToHOL (countdown n))).topAddress
      panSemBitVec64BytesInWord (n+4) (executableState (progToHOL (countdown n))).locals
      (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
      (executableState (progToHOL (countdown n))).ffi (countdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (countdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (countdown n))).locals "x"))
          (executableState (progToHOL (countdown n))).globals (executableState (progToHOL (countdown n))).memory
          (executableState (progToHOL (countdown n))).ffi [.word 0],6*n+9) := by
    simpa only [← countdown_hol_eq] using sourceRun
  have safe : fixtureStackSafe (supportedNative (countdown n)).2.2.2 = true := by
    rw [countdown_native]
    exact countdown_stackSafe n
  have facts : (fixtureRemoveLabels (supportedNative (countdown n)).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative (countdown n)).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative (countdown n)).2.2.2).length % 4 = 0 := by
    rw [countdown_native]
    exact countdown_compiler_facts n
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine (countdown n) (countdown_supported n) witnessContext witnessPrimitive witnessHandler
      (n+4) (6*n+9) (6*n+9) _ _ _ _ 0 run (by omega) (countdown_frame n) safe facts
  rw [countdown_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [countdown_native] using compiled,
    machinePost,ffiPost,by simpa only [countdown_native] using machineRun,events,semantics⟩


private theorem natural_simp (n : Nat) : panSimpProg (naturalCountdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,naturalCountdown,countdownBody]

private theorem natural_words (n : Nat) : supportedWordPrograms (naturalCountdown n) = countdownWordPrograms n := by
  unfold supportedWordPrograms
  rw [natural_simp]
  change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms (naturalCountdownHOL n))) = _
  rw [natural_countdown_crep_code]
  rfl

private theorem natural_native (n : Nat) : (supportedNative (naturalCountdown n)).2.2.2 = countdownNativeStackCode n := by
  simp only [supportedNative,supportedAllocated_eq,natural_words,countdownNativeStackCode]

private theorem natural_frame (n : Nat) : supportedCalleeFrame (naturalCountdown n) ≤
    (fixtureStack (supportedNative (naturalCountdown n)).2.2.2 (fixtureCompilerConfig (supportedNative (naturalCountdown n)).2.2.2)).stack.length := by
  unfold supportedCalleeFrame
  rw [supportedAllocated_eq,natural_words,countdownOptimizedLoop_lookup]
  dsimp only
  rw [nativeEntryFrameSize_compile]
  change 1 + nativeEntryFrameSize countdownZeroLimit (countdownOptimizedLoop n) ≤ _
  rw [countdownCallee_entryFrame_zero]
  exact fixtureStack_nonempty _ _

private theorem natural_wordBound_eq (n budget : Nat) :
    supportedWordBound (naturalCountdown n) budget = supportedWordBound (countdown n) budget := by
  simp only [supportedWordBound,supportedLoopVisits,supportedLoopBudget,supportedCrepBudget,natural_simp,countdown_simp_program]

private theorem natural_ticks (n : Nat) : supportedMachineFactor (naturalCountdown n) * (6*n+9) + supportedMachineOffset (naturalCountdown n) =
    167602730287449600*(6*n+9)+1592247331570371948 := by
  rw [← supportedMachineTicks_affine,← countdown_ticks,← supportedMachineTicks_affine]
  unfold supportedMachineTicks supportedStackBound
  rw [natural_native,countdown_native,natural_words,countdown_words,natural_wordBound_eq]

/-- The natural countdown is independently instantiated from the Phase 7 theorem. -/
theorem naturalCountdownFixture_machine (n : Nat) (range : n < 2^64) :
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (declarations (progToHOL (naturalCountdown n))) = some (fixtureCodeBytes (countdownNativeStackCode n),[4],compilerFinal) ∧
    ∃ machinePost ffiPost, evaluateTargetHOL
      (fixtureMachineConfig (fixtureCodeStart (countdownNativeStackCode n))) sourceFfi
      (167602730287449600*(6*n+9)+1592247331570371948)
      (fixtureMachineState (countdownNativeStackCode n)) = (.halt .success,machinePost,ffiPost) ∧
      FfiEventListRel (executableState (progToHOL (naturalCountdown n))).ffi.ioEvents ffiPost.ioEvents ∧
      PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (declarations (progToHOL (naturalCountdown n))) = .terminate .success ffiPost.ioEvents := by
  have actual := counted_decl_countdown_simplified n (executableState (naturalCountdownHOL n))
    (exactState (naturalCountdownHOL n)) (source_related _) (source_ranged _) "x" countdown_name_ranged range
    (by change n ≤ 2^64; omega) 0 witnessContext witnessPrimitive witnessHandler [] 0
  obtain ⟨result,_,sourceRun,_,_,resultEq⟩ := actual
  subst result
  have run : evalPanValueFfiProgSteps witnessContext witnessPrimitive witnessHandler (executableState (progToHOL (naturalCountdown n))).structs []
      (executableState (progToHOL (naturalCountdown n))).baseAddress (executableState (progToHOL (naturalCountdown n))).topAddress
      panSemBitVec64BytesInWord (n+3) (executableState (progToHOL (naturalCountdown n))).locals
      (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
      (executableState (progToHOL (naturalCountdown n))).ffi (naturalCountdown n)
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL (naturalCountdown n))))) =
        some (.returned (restorePanValueLocal (fun _ => none) "x" ((executableState (progToHOL (naturalCountdown n))).locals "x"))
          (executableState (progToHOL (naturalCountdown n))).globals (executableState (progToHOL (naturalCountdown n))).memory
          (executableState (progToHOL (naturalCountdown n))).ffi [.word 0],6*n+7) := by
    simpa [naturalCountdownHOL,naturalCountdown] using sourceRun
  have safe : fixtureStackSafe (supportedNative (naturalCountdown n)).2.2.2 = true := by
    rw [natural_native]
    exact countdown_stackSafe n
  have facts : (fixtureRemoveLabels (supportedNative (naturalCountdown n)).2.2.2).isSome = true ∧
      (fixtureCodeBytes (supportedNative (naturalCountdown n)).2.2.2).length ≤ 0xecc ∧
      (fixtureCodeBytes (supportedNative (naturalCountdown n)).2.2.2).length % 4 = 0 := by
    rw [natural_native]
    exact countdown_compiler_facts n
  obtain ⟨compilerFinal,compiled,machinePost,ffiPost,machineRun,events,semantics⟩ :=
    supported_counted_machine (naturalCountdown n) (naturalCountdown_supported n) witnessContext witnessPrimitive witnessHandler
      (n+3) (6*n+7) (6*n+9) _ _ _ _ 0 run (by omega) (natural_frame n) safe facts
  rw [natural_ticks] at machineRun
  exact ⟨compilerFinal,by simpa only [natural_native] using compiled,
    machinePost,ffiPost,by simpa only [natural_native] using machineRun,events,semantics⟩

end SteppedFlapjack.Concrete
