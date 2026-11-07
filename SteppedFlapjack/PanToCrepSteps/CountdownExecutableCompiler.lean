import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsm

/-! Connect the complete callable compiler output to the countdown Lab code. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- Successful complete executable compilation supplies the exact bytes,
Lab configuration and bitmap list used by the countdown machine theorem. -/
theorem countdown_executableCompiler_lab
    (name : MlString) (initial returned : BitVec 64)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (target : mc.target = riscvTarget) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (final : Backend.Config) (stackMax : Option Nat)
    (hcompile : compileProgMaxAsmExecutable countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = (some (bytes,bitmaps,final),stackMax)) :
    LabToTarget.compile riscvConfig countdownRiscVBackend.labConf
      (countdownStackLabCode name initial returned countdownRiscVBackend) = some (bytes,final.labConf) ∧
    (countdownNativeRiscV name initial returned countdownRiscVBackend.wordToWordConf).1 = bitmaps := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  have hc : compileProgMax countdownRiscVBackend mc source = (some (bytes,bitmaps,final),stackMax) := by
    rw [← compileProgMaxAsmExecutable_eq]
    simpa only [target,riscvTarget,source] using hcompile
  obtain ⟨col,wprog,wconf,frames,program,labConf,hw,hs,hlab,hfinal,_⟩ :=
    compileProgMax_some countdownRiscVBackend mc source bytes bitmaps final stackMax hc
  have hw' : WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa source) = (col,wprog) := by
    simpa only [target,riscvTarget] using hw
  have hs' : WordToStack.Native.compileNative riscvConfig false wprog = (bitmaps,wconf,frames,program) := by
    simpa only [target,riscvTarget] using hs
  have hnative : countdownNativeRiscV name initial returned countdownRiscVBackend.wordToWordConf =
      (bitmaps,wconf,frames,program) := by
    change WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa source)).2 = _
    rw [hw']
    exact hs'
  have hcode : countdownStackLabCode name initial returned countdownRiscVBackend =
      StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf
        (2 * DataToWord.maxHeapLimit 64 countdownRiscVBackend.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset program := by
    simp only [countdownStackLabCode,hnative]
  have hconf : final.labConf = labConf := by rw [hfinal]
  constructor
  · simpa only [target,riscvTarget,← hcode,← hconf] using hlab
  · simp only [hnative]

end SteppedFlapjack.PanToCrepSteps
