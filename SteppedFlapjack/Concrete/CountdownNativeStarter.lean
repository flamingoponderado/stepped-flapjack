import SteppedFlapjack.Concrete.CountdownInitE
import SteppedFlapjack.Concrete.TwoProgramNativeEntry
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
namespace SteppedFlapjack.Concrete

/-- The native Word initializer for the actual countdown Stack state. -/
noncomputable def countdownFixtureWord (n : Nat) (cfg : LabToTarget.Config) :=
  fixtureWord (countdownNativeStackCode n)
    (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2 cfg

theorem countdownFixture_entryFrame (n : Nat) (cfg : LabToTarget.Config) : sptLookup 64 (countdownFixtureWord n cfg).stackSize = some 0 := by
  exact twoProgram_optimizedEntry_frame riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n))) (naturalCountdown_scalar n)
    (countdownNativeStackCode n) cfg
end SteppedFlapjack.Concrete
namespace SteppedFlapjack.Concrete
open SteppedFlapjack.LoopToWordSteps Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The constructed countdown starter is the actual native Word initializer. -/
theorem countdownFixture_starter_eq (n c : Nat) (cfg : LabToTarget.Config) :
    {(countdownWordStarter n (countdownFixtureWord n cfg) 0) with memory := (countdownFixtureStack n cfg).memory, clock := c, code := (countdownFixtureWord n cfg).code} = {(countdownFixtureWord n cfg) with clock := c} := by
  exact fixtureStarter (countdown n) (6*n+9) (countdownLoopBudget n) (naturalCountdownHOL n) (countdownCrepCode n)
    (countdownNativeStackCode n) (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2
    cfg (countdown_nativeGoodCode n) 0 c (countdownFixture_entryFrame n cfg)

/-- The counted source reaches the optimized Word start call from the actual
native initializer, with an explicit Word visit bound. -/
theorem countdownFixture_native_word (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
    let crep := crepStateFrom pan (naturalCountdownHOL n)
    let word := {(countdownFixtureWord n cfg) with clock := 6*countdownLoopVisits n+1}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) word
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 0]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) word ≤ countdownWordBound n := by
  have h := countdownFixture_initialized_word n range cfg context primitive handler (countdownFixtureWord n cfg) 0
  have codeEq : (countdownFixtureWord n cfg).code = sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2 := rfl
  dsimp only at h
  rw [← codeEq, countdownFixture_starter_eq] at h
  exact h

end SteppedFlapjack.Concrete
