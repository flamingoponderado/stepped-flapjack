import SteppedFlapjack.PanToCrepSteps.SourceFullInitInputs
import SteppedFlapjack.LoopToWordSteps.FullInitMachineConstruct
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget
import Flapjack.RiscV.CorrectnessEncoding.Complete

/-! Concrete native RISC-V configuration facts for the source bound. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target


open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc
open SteppedFlapjack.LoopToWordSteps

/-- The Lab initializer guards excluding the proved RISC-V configuration, empty oracle and compiler-derived no-install conditions. -/
def LabMachineInitGuardsCore
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (_coracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) : Prop :=
  goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧
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

/-- Add the separately proved no-install fact to the remaining initializer guards. -/
theorem labMachineInitGuards_of_core
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → Config × LabProgHOL 64) (names : List HolFfiName) (info newInfo : List ShmemInfoNum)
    (core : LabMachineInitGuardsCore mc ms code code2 labs clock i cbspace t m dm sdm coracle names info newInfo)
    (config : mcConfOk mc)
    (oracleOk : noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames)
    (noInstall : noInstallOrNoShareMem code mc.ffiNames) :
    LabMachineInitGuards mc ms code code2 labs clock i cbspace t m dm sdm coracle names info newInfo := by
  rcases core with ⟨a,d,e,f,g,h,j,k,l,n,last⟩
  exact ⟨a,config,oracleOk,d,e,f,g,h,j,k,l,n,noInstall,last⟩

/-- An empty installation oracle meets the compiler contract when its stored
configuration names the actual labels, byte position and FFI interface. -/
theorem emptyLabCompilerOracleOk (config : Config) (labels : Spt (Spt Nat)) (position : Nat)
    (ac : AsmConfigExact 64) (ffis : List HolFfiName)
    (hlabs : config.labels = labels) (hpos : config.pos = position) (hffi : config.ffiNames = some ffis) :
    compilerOracleOk (fun _ => (config, ([] : LabProgHOL 64))) labels position ac ffis := by
  refine ⟨fun _ => ?_,⟨hlabs,hpos,hffi⟩⟩
  simp [goodCode,LabProps.noShareMemInst,LabProps.LabelSets.getLabels,
    BackendProps.restrictNonzero,LabProps.allEncOkPreHOL,LabSem.asmFetchAux]

/-- A no-install Stack oracle forces the Lab initializer's compiler oracle to
be the constant empty-code oracle. -/
theorem labOracle_empty_of_stackInit {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64)) (code : List (Nat × StackLang.HolProg 64))
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState F) (labCode : LabProgHOL 64) (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64)
    (dm sdm : BitVec 64 → Bool) (cbpos : BitVec 64) (cbspace : Nat) (labOracle : Nat → Config × LabProgHOL 64)
    (stackInit : StackToLab.Proofs.FullMakeInitSemantics.Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      (LabToTarget.makeInit mc ffi asm memory dm sdm machine labCode (LabToTarget.compileLab mc.target.config) cbpos cbspace labOracle)
      saveRegs dataSp (fun _ => (cfg,[],[]))) :
    labOracle = fun _ => (cfg,[]) := by
  have h := stackInit.2.2.1
  simpa [LabToTarget.makeInit,StackToLab.compileNoStubs,StackNames.compileHOL] using h

/-- The original RISC-V assembler leaves 22 allocatable registers after the
compiler's reserved and avoided registers. -/
theorem riscvConfig_allocatable_registers :
    riscvConfig.regCount-(5+riscvConfig.avoidRegs.length) = 22 := by
  decide

/-- The native initialization bound requires only four such registers. -/
theorem riscvConfig_native_registers :
    4 < riscvConfig.regCount-(5+riscvConfig.avoidRegs.length) := by
  rw [riscvConfig_allocatable_registers]
  decide

/-- A machine configured for the original RISC-V target uses the same
assembler configuration as the native compiler. -/
theorem riscvTarget_assembler_config
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (target : mc.target = riscvTarget) : mc.target.config = riscvConfig := by
  rw [target]
  rfl

/-- The original RISC-V encoder and standard argument-register choices
discharge the machine configuration contract. -/
theorem riscvTarget_mcConfOk
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11)
    (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13) :
    mcConfOk mc := by
  unfold mcConfOk
  rw [target,ptr,len,ptr2,len2]
  refine ⟨by simp [goodDimindex],Flapjack.RiscV.TargetProof.riscv_encoder_correct,?_,?_,?_,?_,?_,
    Flapjack.RiscV.TargetProof.riscv_enc_ok⟩ <;> decide

end SteppedFlapjack.PanToCrepSteps
