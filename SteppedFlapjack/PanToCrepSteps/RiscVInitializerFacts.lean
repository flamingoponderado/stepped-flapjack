import SteppedFlapjack.PanToCrepSteps.CountdownCanonicalSource
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget
import Flapjack.RiscV.CorrectnessEncoding.Complete

/-! Concrete native RISC-V configuration facts for the source bound. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target


open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget Flapjack.Misc
open SteppedFlapjack.LoopToWordSteps

/-- The Lab initializer guards excluding the proved RISC-V configuration and compiler-derived no-install conditions. -/
def LabMachineInitGuardsCore
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) : Prop :=
  goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧
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
    (noInstall : noInstallOrNoShareMem code mc.ffiNames) :
    LabMachineInitGuards mc ms code code2 labs clock i cbspace t m dm sdm coracle names info newInfo := by
  rcases core with ⟨a,c,d,e,f,g,h,j,k,l,n,last⟩
  exact ⟨a,config,c,d,e,f,g,h,j,k,l,n,noInstall,last⟩

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

/-- The actual compiled countdown has no installation instruction, so it
satisfies the Lab initializer's no-install/no-shared-memory disjunction. -/
theorem countdown_compiled_noInstall (name : Flapjack.Basis.Pure.MlString.MlString)
    (initial returned : BitVec 64) (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (stackConf : Flapjack.Compiler.Backend.StackToLab.Config) (dataConf : Flapjack.Compiler.Backend.DataToWord.Config)
    (limit registers : Nat) (offset : BitVec 64 × BitVec 64) (ffis : List HolFfiName) :
    let source := singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
      (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))
    let word := Flapjack.Compiler.Backend.WordToWord.compile wc riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa source)
    let native := Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false word.2
    Flapjack.Compiler.Backend.LabToTarget.noInstallOrNoShareMem
      (Flapjack.Compiler.Backend.StackToLab.compile stackConf dataConf limit registers offset native.2.2.2) ffis := by
  let source := singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
    (.dec name .one (.const initial) (.seq .skip (.seq
      (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
      (.return (.const returned)))))
  let wprog := panToWordCompileProgHOL riscvConfig.isa source
  let word := Flapjack.Compiler.Backend.WordToWord.compile wc riscvConfig wprog
  let native := Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false word.2
  apply Flapjack.Pancake.Proofs.PanToTarget.panToTargetNoInstallOrNoShareMem source riscvConfig riscvConfig.isa
    wprog wc word.1 word.2 native.1 native.2.1 native.2.2.1 native.2.2.2 stackConf dataConf limit registers offset ffis
  refine ⟨?_,?_,rfl,?_,?_⟩
  · simp [source,singleEntryProgram,Flapjack.Pancake.PanLang.functionsHOL]
  · decide
  · exact Prod.mk.eta.symm
  · simp only [Prod.mk.eta]
    rfl

/-- Native Stack output for the original singleton countdown. -/
noncomputable def countdownNativeRiscV (name : Flapjack.Basis.Pure.MlString.MlString)
    (initial returned : BitVec 64) (wc : Flapjack.Compiler.Backend.WordToWord.Config) :=
  Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false
    (Flapjack.Compiler.Backend.WordToWord.compile wc riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
        (.dec name .one (.const initial) (.seq .skip (.seq
          (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
          (.return (.const returned)))))))).2

/-- The Stack initializer's code equality turns the compiler-derived fact
into the Lab guard, with no separate no-install premise. -/
theorem countdown_lab_noInstall_from_stackInit {F : Type}
    (name : Flapjack.Basis.Pure.MlString.MlString) (initial returned : BitVec 64)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (stackConf : Flapjack.Compiler.Backend.StackToLab.Config) (dataConf : Flapjack.Compiler.Backend.DataToWord.Config)
    (limit registers : Nat) (offset : BitVec 64 × BitVec 64) (dataSp : Nat)
    (saveRegs : Nat → Bool) (oracle : Nat → Flapjack.Compiler.Backend.LabToTarget.Config ×
      List (Nat × Flapjack.Compiler.Backend.StackLang.HolProg 64) × List (BitVec 64))
    (lab : Flapjack.Compiler.Backend.LabSem.State 64 Flapjack.Compiler.Backend.LabToTarget.Config F)
    (ffis : List HolFfiName)
    (stackInit : Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      stackConf dataConf limit registers offset (countdownNativeRiscV name initial returned wc).1
      (countdownNativeRiscV name initial returned wc).2.2.2 lab saveRegs dataSp oracle) :
    Flapjack.Compiler.Backend.LabToTarget.noInstallOrNoShareMem lab.code ffis := by
  have compiled := countdown_compiled_noInstall name initial returned wc stackConf dataConf limit registers offset ffis
  have codeEq := stackInit.2.1
  rw [codeEq]
  simpa only [countdownNativeRiscV] using compiled

end SteppedFlapjack.PanToCrepSteps
