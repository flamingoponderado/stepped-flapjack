import SteppedFlapjack.Concrete.CountdownSourceLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.StackToLabSteps
namespace SteppedFlapjack.Concrete

/-- The unprefixed source uses the same initialized Lab run at clock `6*n+9`. -/
theorem naturalCountdownFixture_source_lab (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config) (ms : RiscV.L3.riscv_state)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL (naturalCountdown n))) = countdownWordPrograms n ∧
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit)
      (labPost : LabSem.State 64 LabToTarget.Config Unit),
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState (naturalCountdown n)
        (clockedFixtureSource (naturalCountdown n) (6*n+9))) (naturalCountdownHOL n)) (naturalCrepEntry n) =
        (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      LabSem.evaluate {(fixtureTargetLab (countdownNativeStackCode n) cfg ms) with clock :=
        (1060776773971200*n + 3270750953752551)} =
        (.halt .success,labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  refine ⟨naturalCountdown_panToWord n,?_⟩
  have h := countdownFixture_source_lab n range cfg ms context primitive handler
  rw [countdownFixtures_crep_equal n (6*n+9)] at h
  exact h
end SteppedFlapjack.Concrete
