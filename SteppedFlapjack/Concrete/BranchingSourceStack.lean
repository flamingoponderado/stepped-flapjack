import SteppedFlapjack.Concrete.TwoProgramStack
import SteppedFlapjack.Concrete.FixedWordBounds
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordToStackSteps
namespace SteppedFlapjack.Concrete

/-- The comparison source reaches the actual initialized Stack program. -/
theorem comparisonFixture_source_stack (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config Unit) (targetResult : Option (StackSemResult 64)),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branching
        (clockedFixtureSource branching 6)) branchingHOL) branchCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      targetPost.ffi = post.ffi ∧
      StackSemEvaluate.evaluate (.call none (.inl 64) none,
        {(comparisonFixtureStack cfg) with clock := comparisonWordBound+1}) = (targetResult,targetPost) ∧
      targetResult = some (compileResult (.result (.loc 1 0) [.word 7])) ∧
      StackSteps.steps (.call none (.inl 64) none,
        {(comparisonFixtureStack cfg) with clock := comparisonWordBound+1}) ≤
        860921207 := by
  obtain ⟨final,post,run,state,result,ffi,bound⟩ := comparisonFixture_native_word cfg context primitive handler
  obtain ⟨targetPost,targetResult,targetRun,targetResultEq,targetFfi,targetBound⟩ :=
    twoProgram_fixture_stack riscvConfig.isa (ofString "main") (entryName branchingHOL) branchCrepBody
      (Ne.symm (entryName_fresh branchingHOL)) branching_scalar cfg (6*comparisonLoopVisits) comparisonWordBound 7
      comparison_nativeGoodCode (comparison_fixture_callee_frame cfg) result bound
  change StackSteps.steps (.call none (.inl 64) none,{(comparisonFixtureStack cfg) with clock := comparisonWordBound+1}) ≤
    nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms 64
      (loopToWordCompFuncHOL 64 [] branchingLoopEntry) comparisonWordBound at targetBound
  have closed : nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms 64
      (loopToWordCompFuncHOL 64 [] branchingLoopEntry) comparisonWordBound = 860921207 := by
    rw [comparison_stackBound_closed,comparison_bound_closed]
  rw [closed] at targetBound
  exact ⟨final,post,targetPost,targetResult,run,state,targetFfi.trans ffi,targetRun,targetResultEq,targetBound⟩

/-- The branching-loop source reaches the actual initialized Stack program. -/
theorem branchingLoopFixture_source_stack (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config Unit) (targetResult : Option (StackSemResult 64)),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branchingLoop
        (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop)) branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      targetPost.ffi = post.ffi ∧
      StackSemEvaluate.evaluate (.call none (.inl 64) none,
        {(branchingLoopFixtureStack cfg) with clock := branchWordBound+1}) = (targetResult,targetPost) ∧
      targetResult = some (compileResult (.result (.loc 1 0) [.word 7])) ∧
      StackSteps.steps (.call none (.inl 64) none,
        {(branchingLoopFixtureStack cfg) with clock := branchWordBound+1}) ≤
        348971665463 := by
  obtain ⟨final,post,run,state,result,ffi,bound⟩ := branchingLoopFixture_native_word cfg context primitive handler
  obtain ⟨targetPost,targetResult,targetRun,targetResultEq,targetFfi,targetBound⟩ :=
    twoProgram_fixture_stack riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody
      (Ne.symm (entryName_fresh (progToHOL branchingLoop))) branchingLoop_scalar cfg (6*branchLoopVisits) branchWordBound 7
      branchingLoop_nativeGoodCode (branch_fixture_callee_frame cfg) result bound
  change StackSteps.steps (.call none (.inl 64) none,{(branchingLoopFixtureStack cfg) with clock := branchWordBound+1}) ≤
    nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms 64
      (loopToWordCompFuncHOL 64 [] branchingLoopEntry) branchWordBound at targetBound
  have closed : nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms 64
      (loopToWordCompFuncHOL 64 [] branchingLoopEntry) branchWordBound = 348971665463 := by
    rw [branch_stackBound_closed,branch_bound_closed]
  rw [closed] at targetBound
  exact ⟨final,post,targetPost,targetResult,run,state,targetFfi.trans ffi,targetRun,targetResultEq,targetBound⟩
end SteppedFlapjack.Concrete
