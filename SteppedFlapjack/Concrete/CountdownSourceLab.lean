import SteppedFlapjack.Concrete.NaturalCountdownSourceStack
import SteppedFlapjack.Concrete.FixtureStackLab
import SteppedFlapjack.StackToLabSteps.EntryLocation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
namespace SteppedFlapjack.Concrete

/-- A counted countdown source reaches the Lab program generated from its
actual Stack code, with an explicit clock computed from the fixture inputs. -/
theorem countdownFixture_source_lab (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (labPost : LabSem.State 64 LabToTarget.Config Unit),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState (countdown n)
        (clockedFixtureSource (countdown n) (6*n+9))) (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      LabSem.evaluate {(fixtureTargetLab (countdownNativeStackCode n) cfg ms) with clock := (fixtureLabTickLimit (countdownNativeStackCode n) cfg (9543650688*n+29426459323))} =
        (.halt .success,labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨final,post,targetPost,targetResult,sourceRun,stateRel,ffi,stackRun,result,stackBound⟩ :=
    countdownFixture_source_stack n range cfg context primitive handler
  have exactResult : targetResult = some (.result (.loc 1 0)) := by simpa [compileResult] using result.symm
  rw [exactResult] at stackRun
  have run : StackSemEvaluate.evaluate (.call none (.inl 64) none,
      {(fixtureStack (countdownNativeStackCode n) cfg) with clock := countdownWordBound n+1}) =
      (some (.result (.loc 1 0)),targetPost) := by simpa only [countdownFixtureStack] using stackRun
  have bound : StackSteps.steps (.call none (.inl 64) none,
      {(fixtureStack (countdownNativeStackCode n) cfg) with clock := countdownWordBound n+1}) ≤ 9543650688*n+29426459323 := by
    simpa only [countdownFixtureStack] using stackBound
  obtain ⟨labPost,labRun,labFfi⟩ := fixtureStack_lab_return (countdownNativeStackCode n) cfg ms (countdown_nativeGoodCode n)
    (countdownWordBound n+1) (9543650688*n+29426459323) targetPost run bound
  exact ⟨final,post,labPost,sourceRun,stateRel,labRun,labFfi.trans (congrArg _ ffi)⟩
end SteppedFlapjack.Concrete
