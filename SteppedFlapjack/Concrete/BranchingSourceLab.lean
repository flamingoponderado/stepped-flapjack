import SteppedFlapjack.Concrete.BranchingSourceStack
import SteppedFlapjack.Concrete.BranchingLabBounds
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.WordToStackProofs.CompCorrect Flapjack.Pancake.PanLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
namespace SteppedFlapjack.Concrete

/-- The comparison source reaches its compiled Lab program with matching events. -/
theorem comparisonFixture_source_lab (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (labPost : LabSem.State 64 LabToTarget.Config Unit),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branching
        (clockedFixtureSource branching 6)) branchingHOL) branchCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      LabSem.evaluate {(fixtureTargetLab comparisonNativeCode cfg ms) with clock :=
        27156840326100392288867315340591} = (.halt .success,labPost) ∧
      labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨final,post,targetPost,targetResult,sourceRun,stateRel,ffi,stackRun,result,stackBound⟩ :=
    comparisonFixture_source_stack cfg context primitive handler
  have exactResult : targetResult = some (.result (.loc 1 0)) := by simpa [compileResult] using result
  rw [exactResult] at stackRun
  have run : StackSemEvaluate.evaluate (.call none (.inl 64) none,
      {(fixtureStack comparisonNativeCode cfg) with clock := comparisonWordBound+1}) =
      (some (.result (.loc 1 0)),targetPost) := by simpa only [comparisonFixtureStack] using stackRun
  have bound : StackSteps.steps (.call none (.inl 64) none,
      {(fixtureStack comparisonNativeCode cfg) with clock := comparisonWordBound+1}) ≤ 860921207 := by
    simpa only [comparisonFixtureStack] using stackBound
  obtain ⟨labPost,labRun,labFfi⟩ := fixtureStack_lab_return comparisonNativeCode cfg ms comparison_nativeGoodCode
    (comparisonWordBound+1) 860921207 targetPost run bound
  rw [comparisonLabTick_closed cfg] at labRun
  exact ⟨final,post,labPost,sourceRun,stateRel,labRun,labFfi.trans (congrArg _ ffi)⟩

/-- The branching-loop source reaches its compiled Lab program with matching events. -/
theorem branchingLoopFixture_source_lab (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (labPost : LabSem.State 64 LabToTarget.Config Unit),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branchingLoop
        (clockedFixtureSource branchingLoop 23)) (progToHOL branchingLoop)) branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      LabSem.evaluate {(fixtureTargetLab branchingLoopNativeCode cfg ms) with clock :=
        11007938613030372157139427543278511} = (.halt .success,labPost) ∧
      labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨final,post,targetPost,targetResult,sourceRun,stateRel,ffi,stackRun,result,stackBound⟩ :=
    branchingLoopFixture_source_stack cfg context primitive handler
  have exactResult : targetResult = some (.result (.loc 1 0)) := by simpa [compileResult] using result
  rw [exactResult] at stackRun
  have run : StackSemEvaluate.evaluate (.call none (.inl 64) none,
      {(fixtureStack branchingLoopNativeCode cfg) with clock := branchWordBound+1}) =
      (some (.result (.loc 1 0)),targetPost) := by simpa only [branchingLoopFixtureStack] using stackRun
  have bound : StackSteps.steps (.call none (.inl 64) none,
      {(fixtureStack branchingLoopNativeCode cfg) with clock := branchWordBound+1}) ≤ 348971665463 := by
    simpa only [branchingLoopFixtureStack] using stackBound
  obtain ⟨labPost,labRun,labFfi⟩ := fixtureStack_lab_return branchingLoopNativeCode cfg ms branchingLoop_nativeGoodCode
    (branchWordBound+1) 348971665463 targetPost run bound
  rw [branchingLoopLabTick_closed cfg] at labRun
  exact ⟨final,post,labPost,sourceRun,stateRel,labRun,labFfi.trans (congrArg _ ffi)⟩
end SteppedFlapjack.Concrete
