import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.InitEStack
import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Compiler.Backend.WordToStack.Native

namespace SteppedFlapjack.Concrete

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The witness Word table is the original Pancake compiler output. -/
theorem countdown_panToWord (n : Nat) :
    panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") (progToHOL (countdown n))) = countdownWordPrograms n := by
  have h := singleEntry_countdown_panToWord riscvConfig.isa (ofString "x") (BitVec.ofNat 64 n) 0
  have code := natural_countdown_crep_code n
  unfold crepPrograms declarations at code
  dsimp only at h
  simp only [naturalCountdownHOL,naturalCountdown,countdownBody,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil] at code
  rw [code] at h
  simpa [countdownWordPrograms,countdownCrepCode,twoPrograms,phase3CountdownCrepBody, countdown,progToHOL,expToHOL,shapeToHOL,countdownBody,naturalCountdownHOL,naturalCountdown] using h

/-- The original compiler guarantees the countdown Stack table is well formed. -/
theorem countdown_nativeGoodCode (n : Nat) : StackToLab.Proofs.GoodCode.goodCode 24
    (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2 := by
  let pan := singleEntryProgram (ofString "main") (progToHOL (countdown n))
  let w := WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)
  let st := compileNative riscvConfig false w.2
  have h := Flapjack.Pancake.Proofs.PanToTarget.word_to_stack_good_code_lemma countdownRiscVBackend countdownMachineConfig
    pan w.1 w.2 st.1 st.2.1 st.2.2.1 st.2.2.2
  have hw : WordToWord.compile countdownRiscVBackend.wordToWordConf countdownMachineConfig.target.config
        (panToWordCompileProgHOL countdownMachineConfig.target.config.isa pan) = (w.1,w.2) := by
    change WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa pan) = _
    rw [show panToWordCompileProgHOL riscvConfig.isa pan = countdownWordPrograms n from countdown_panToWord n]
  have hs : compileNative countdownMachineConfig.target.config false w.2 = (st.1,st.2.1,st.2.2.1,st.2.2.2) := by rfl
  have hn : ((functionsHOL pan).map Prod.fst).Nodup := by simp [pan,singleEntryProgram,functionsHOL]
  have hg := h ⟨hw,by decide,hs,by decide,hn⟩
  exact hg

/-- Actual compiled Stack code for the countdown. -/
noncomputable def countdownNativeStackCode (n : Nat) : List (Nat × StackLang.HolProg 64) :=
  (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2).2.2.2

/-- Actual fullMakeInit Stack state for the countdown and concrete Lab layout. -/
noncomputable def countdownFixtureStack (n : Nat) (cfg : LabToTarget.Config) := fixtureStack (countdownNativeStackCode n) cfg

/-- Native initialization holds for the actual countdown Stack state. -/
theorem countdownFixture_initOk (n : Nat) (cfg : LabToTarget.Config) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (countdownFixtureStack n cfg) (fixtureWordOracle cfg) :=
  fixtureStack_nativeInitOk _ cfg (countdown_nativeGoodCode n)

open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps

/-- A bounded optimized countdown run simulates on the actual initialized Stack state. -/
theorem countdownFixture_stack_span (n clock limit : Nat) (cfg : LabToTarget.Config)
    (result : Option (WordSemResult 64)) (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Unit)
    (run : evaluate countdownOptimizedEntry {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock} = (result,post))
    (notError : result ≠ some .error) (notTimeout : result ≠ some .timeOut)
    (complete : CompleteWordResult result)
    (bound : SteppedFlapjack.WordSteps.steps countdownOptimizedEntry
      {(countdownInitialWord n (countdownFixtureStack n cfg) (fixtureWordOracle cfg)) with clock := clock} ≤ limit) :
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (.call none (.inl 64) none,{(countdownFixtureStack n cfg) with clock := limit+1}) = (targetResult,targetPost) ∧
      result.map compileResult = targetResult ∧ post.ffi = targetPost.ffi ∧
      SteppedFlapjack.StackSteps.steps (.call none (.inl 64) none,{(countdownFixtureStack n cfg) with clock := limit+1}) ≤
        nativeTailEntryBound countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n) 64 (countdownSourceWordEntry n) limit := by
  apply countdown_stack_span n clock limit (countdownFixtureStack n cfg) (fixtureWordOracle cfg)
  · exact fixtureStack_code _ cfg
  · rw [countdown_native_bitmaps]
    change [4] <+: (fixtureStack (countdownNativeStackCode n) cfg).bitmaps
    rw [fixtureStack_bitmaps]
  · exact countdownFixture_initOk n cfg
  · exact fixtureStack_nonempty _ cfg
  · exact run
  · exact notError
  · exact notTimeout
  · exact complete
  · exact bound

end SteppedFlapjack.Concrete
