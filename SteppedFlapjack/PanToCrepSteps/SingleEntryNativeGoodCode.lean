import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.WordToStack.Native
namespace SteppedFlapjack.PanToCrepSteps

/-- Original compilation guarantees good Stack code for a singleton source. -/
theorem singleEntry_nativeGoodCode (body : ProgHOL 64) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (compiled : panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") body) = words) :
    StackToLab.Proofs.GoodCode.goodCode 24
      (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2 := by
  let pan := singleEntryProgram (ofString "main") body
  let w := WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words
  let st := compileNative riscvConfig false w.2
  have h := Flapjack.Pancake.Proofs.PanToTarget.word_to_stack_good_code_lemma countdownRiscVBackend countdownMachineConfig
    pan w.1 w.2 st.1 st.2.1 st.2.2.1 st.2.2.2
  have hw : WordToWord.compile countdownRiscVBackend.wordToWordConf countdownMachineConfig.target.config
        (panToWordCompileProgHOL countdownMachineConfig.target.config.isa pan) = (w.1,w.2) := by
    change WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa pan) = _
    rw [compiled]
  have hs : compileNative countdownMachineConfig.target.config false w.2 = (st.1,st.2.1,st.2.2.1,st.2.2.2) := by rfl
  have hn : ((functionsHOL pan).map Prod.fst).Nodup := by simp [pan,singleEntryProgram,functionsHOL]
  exact h ⟨hw,by decide,hs,by decide,hn⟩
end SteppedFlapjack.PanToCrepSteps
