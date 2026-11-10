import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts

/-! Construct the full backend from the actual Lab initializer. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Misc

/-- The original Lab initializer guards, with the actual machine, code,
label-removal result, FFI and memory data. -/
def LabMachineInitGuards
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) : Prop :=
  goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧ mcConfOk mc ∧
  (noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
    mc.target.config mc.ffiNames) ∧
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
  noInstallOrNoShareMem code mc.ffiNames ∧
  (∀ bn, bn < cbspace → BitVec.ofNat 64 bn + BitVec.ofNat 64 (progToBytes code2).length +
    mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)

/-- Derive the full machine context from Lab initialization guards and the
Stack-to-Lab initializer assumptions, aligning both the data and shared word domains. -/
noncomputable def fullInitMachineContext_of_alignedFilteredLabInit {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (inputCode : List (Nat × HolProg 64)) (saveRegs : Nat → Bool) (dataSp : Nat)
    (stackOracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (ffi : HolFfiState F) (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace labClock : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (labOracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (guards : LabMachineInitGuards mc ms (LabFilter.filterSkip code) code2 labs labelClock i cbspace t m dm sdm
      (fun n => ((labOracle n).1,LabFilter.filterSkip (labOracle n).2)) newFfiNames shmemInfo newShmemInfo)
    (stackInit : Assumptions stackConf dataConf maxHeap sp offset bitmaps inputCode
      (LabToTarget.makeInit mc ffi t m (fun a => dm a && holByteAligned a) (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp stackOracle) :
    let lab := {LabToTarget.makeInit mc ffi t m (fun a => dm a && holByteAligned a) (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle with clock := labClock}
    FullInitMachineContext (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp stackOracle).1 := by
  let lab0 := LabToTarget.makeInit mc ffi t m dm sdm ms code (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle
  let filteredOracle := fun n => ((labOracle n).1,LabFilter.filterSkip (labOracle n).2)
  let filteredLab := LabToTarget.makeInit mc ffi t m dm sdm ms (LabFilter.filterSkip code)
    (compileLab mc.target.config) (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace filteredOracle
  have rel := makeInit_stateRel mc ms ffi (LabFilter.filterSkip code) code2 labs labelClock i cbspace t m dm sdm
    filteredOracle newFfiNames shmemInfo newShmemInfo guards
  have tie := oracleTie_makeInit mc ffi t m dm sdm ms (LabFilter.filterSkip code) (compileLab mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace filteredOracle
  have filterRel := SteppedFlapjack.LabToTargetSteps.makeInit_filterRel mc ffi t m dm sdm ms code
    (compileLab mc.target.config) (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle
  have filterClock : LabFilter.Proofs.stateRel {filteredLab with clock := labClock} {lab0 with clock := labClock} := by
    exact SteppedFlapjack.LabToTargetSteps.filterRel_withClock _ _ labClock filterRel
  exact {
    stackConf := stackConf, dataConf := dataConf, maxHeap := maxHeap, sp := sp, offset := offset,
    bitmaps := bitmaps, inputCode := inputCode, lab := LabProps.alignSdm (LabProps.alignDm {lab0 with clock := labClock}), saveRegs := saveRegs,
    dataSp := dataSp, coracle := stackOracle,
    initAssumptions := by
      change Assumptions stackConf dataConf maxHeap sp offset bitmaps inputCode
        {LabToTarget.makeInit mc ffi t m (fun a => dm a && holByteAligned a) (fun a => sdm a && holByteAligned a) ms code
          (LabToTarget.compile mc.target.config)
          (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle with clock := labClock}
        saveRegs dataSp stackOracle
      simpa [Assumptions,StackToLab.Proofs.MakeInit.memoryAssumption,LabProps.alignSdm,LabProps.alignDm] using stackInit,
    stackEq := rfl, pc := mc.target.getPc ms, mc := mc, labCode := code2, labs := labs, asm := t,
    machine := ms, hmc := hmc, machineLab := {filteredLab with clock := labClock}, labRelation := Or.inr (Or.inr (Or.inr ⟨{lab0 with clock := labClock},rfl,filterClock⟩)),
    tie := by simpa [oracleTie,filteredLab] using tie,
    machineRel := by simpa [filteredLab] using stateRelClock _ filteredLab t ms labClock rel }

end SteppedFlapjack.LoopToWordSteps
