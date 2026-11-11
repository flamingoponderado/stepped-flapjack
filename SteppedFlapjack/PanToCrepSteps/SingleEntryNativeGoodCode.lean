import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.WordToStack.Native
namespace SteppedFlapjack.PanToCrepSteps

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
/-- Original compilation guarantees good Stack code for distinct source functions. -/
theorem source_nativeGoodCode (pan : List (DeclHOL 64))
    (unique : ((functionsHOL pan).map Prod.fst).Nodup) :
    StackToLab.Proofs.GoodCode.goodCode 24
      (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa pan)).2).2.2.2 := by
  generalize hw : WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
    (panToWordCompileProgHOL riscvConfig.isa pan) = compiled
  obtain ⟨colours,words⟩ := compiled
  generalize hs : compileNative riscvConfig false words = native
  obtain ⟨bitmaps,config,names,code⟩ := native
  have h := Flapjack.Pancake.Proofs.PanToTarget.word_to_stack_good_code_lemma countdownRiscVBackend countdownMachineConfig
    pan colours words bitmaps config names code
  have good := h ⟨hw,by decide,hs,by decide,unique⟩
  have reg : countdownMachineConfig.target.config.regCount -
      (countdownMachineConfig.target.config.avoidRegs.length + 3) = 24 := by decide
  rw [reg] at good
  exact good

/-- Original compilation guarantees good Stack code for a singleton source. -/
theorem singleEntry_nativeGoodCode (body : ProgHOL 64) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (compiled : panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main") body) = words) :
    StackToLab.Proofs.GoodCode.goodCode 24
      (compileNative riscvConfig false (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2 := by
  have unique : ((functionsHOL (singleEntryProgram (ofString "main") body)).map Prod.fst).Nodup := by
    simp [singleEntryProgram,functionsHOL]
  have good := source_nativeGoodCode (singleEntryProgram (ofString "main") body) unique
  rw [compiled] at good
  exact good
end SteppedFlapjack.PanToCrepSteps
