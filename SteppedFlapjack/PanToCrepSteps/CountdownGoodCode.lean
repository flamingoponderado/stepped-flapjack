import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyGoodCodeSource

/-! Source-derived Lab code validity for the actual compiled countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabToTarget

/-- The original countdown has valid Pancake operations. -/
theorem countdown_pancakeGoodCode (name : MlString) (initial returned : BitVec 64) :
    pancakeGoodCodeHOL (singleEntryProgram (ofString "main")
      (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = true := by
  simp [pancakeGoodCodeHOL,singleEntryProgram,goodPanopsHOL,expsOfHOL,everyExpListHOL,everyExpHOL,panopArityTwoHOL]

/-- With the standard backend configuration, the actual compiled countdown
satisfies the Lab good-code initializer guard. -/
theorem countdown_compiled_goodCode (name : MlString) (initial returned : BitVec 64)
    (config : Backend.Config) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (target : mc.target = riscvTarget) (hcfg : backendConfigOk riscvConfig config) :
    let native := countdownNativeRiscV name initial returned config.wordToWordConf
    goodCode riscvConfig (.ln : Spt (Spt Nat))
      (StackToLab.compile config.stackConf config.dataConf (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset native.2.2.2) := by
  let source := singleEntryProgram (ofString "main")
    (.dec name .one (.const initial) (.seq .skip (.seq
      (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
      (.return (.const returned)))))
  have nodup : ((functionsHOL source).map Prod.fst).Nodup := by
    simp [source,singleEntryProgram,functionsHOL]
  have h := Flapjack.Pancake.Proofs.PanToTarget.panToTargetGoodCodeSource (β := Nat)
    config mc source (by rw [target]; exact hcfg) (by simp [goodDimindex])
    (by simp [target,riscvTarget,riscvConfig]) nodup (countdown_pancakeGoodCode name initial returned)
  simpa only [target,riscvTarget,countdownNativeRiscV,source] using h

end SteppedFlapjack.PanToCrepSteps
