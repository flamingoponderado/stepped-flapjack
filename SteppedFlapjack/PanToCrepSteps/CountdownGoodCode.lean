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

open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc

/-- The remaining Lab initialization conditions after deriving code safety,
the RISC-V encoder configuration, the empty oracle and no-install. -/
def LabMachineInitGuardsReduced
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) : Prop :=
  listSubset ((findFfiNames code).filter (fun x => match x with
    | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true ∧
  removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code = some (code2,labs) ∧
  goodInitState mc ms (progToBytes code2) cbspace t m dm sdm ∧
  getShmemInfo code2 0 [] [] = (newFfiNames,shmemInfo) ∧
  newShmemInfo = shmemInfo.map (fun rec => { rec with
    entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
    exitPc := (mc.target.getPc ms).toNat + rec.exitPc }) ∧
  mc.ffiNames.drop i = newFfiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
  newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
  mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index+i))
    (newShmemInfo.map (fun rec => (rec.nbytes,
      HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff), rec.reg,
      BitVec.ofNat 64 rec.exitPc))) ∧
  (∀ bn, bn < cbspace → BitVec.ofNat 64 bn + BitVec.ofNat 64 (progToBytes code2).length +
    mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)

/-- A proved Lab code-safety fact completes the reduced initialization guards. -/
theorem labMachineInitGuardsCore_of_reduced
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) (names : List HolFfiName) (info newInfo : List ShmemInfoNum)
    (codeGood : goodCode mc.target.config (.ln : Spt (Spt Nat)) code)
    (rest : LabMachineInitGuardsReduced mc ms code code2 labs clock i cbspace t m dm sdm names info newInfo) :
    LabMachineInitGuardsCore mc ms code code2 labs clock i cbspace t m dm sdm coracle names info newInfo :=
  ⟨codeGood,rest⟩

end SteppedFlapjack.PanToCrepSteps
