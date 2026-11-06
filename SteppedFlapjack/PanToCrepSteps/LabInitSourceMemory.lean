import SteppedFlapjack.PanToCrepSteps.SourceFullInitInputs
import SteppedFlapjack.LoopToWordSteps.FullInitMachineConstruct

/-! Source memory facts derived directly from the Lab initializer guards. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Misc Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps

/-- The actual Lab initializer guards supply every word read by the constructed source heap. -/
theorem labInit_constructed_source_wordMemory {F : Type}
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
    (guards : LabMachineInitGuards mc ms code code2 labs labelClock i cbspace t m dm sdm
      labOracle newFfiNames shmemInfo newShmemInfo)
    (stackInit : Assumptions stackConf dataConf maxHeap sp offset bitmaps inputCode
      (LabToTarget.makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp stackOracle)
    (template : PanSemStateFiniteExact 64 F) :
    let lab := {LabToTarget.makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle with clock := labClock}
    let stack := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp stackOracle).1
    let backend := fullInitMachineContext_of_labInit stackConf dataConf maxHeap sp offset bitmaps inputCode saveRegs dataSp stackOracle
      mc ms ffi code code2 labs labelClock i cbspace labClock t m dm sdm labOracle newFfiNames shmemInfo newShmemInfo hmc guards stackInit
    ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word := by
  apply labInitializedOriginal_wordMemory_of_goodInit template _ _ mc ms (progToBytes code2) cbspace t m dm sdm
    guards.2.2.2.2.2.1
  rfl

/-- Construct a backend whose native code, bitmap prefix and no-install oracle
come directly from the actual Word-to-Stack compiler output. -/
theorem labInit_native_compiler_source_inputs {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (saveRegs : Nat → Bool) (dataSp : Nat)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
    (ffi : HolFfiState F) (code code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace labClock : Nat) (t : AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (labOracle : Nat → LabToTarget.Config × LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (guards : LabMachineInitGuards mc ms code code2 labs labelClock i cbspace t m dm sdm
      labOracle newFfiNames shmemInfo newShmemInfo)
    (stackInit : Assumptions stackConf dataConf maxHeap sp offset
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2
      (LabToTarget.makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp (fun _ => (cfg,[],[])))
    (template : PanSemStateFiniteExact 64 F) :
    ∃ (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) (backend : FullInitMachineContext stack),
      backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2 ∧
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps ∧
      backend.coracle = (fun _ => (cfg,[],[])) ∧
      backend.mc = mc ∧ backend.machine = ms ∧ backend.lab.clock = labClock ∧
      backend.lab.ffi = ffi ∧ backend.lab.memory = m ∧
      (∀ address, (labInitializedOriginal template stack backend).memaddrs address →
        ∃ word, backend.lab.memory address = .word word) := by
  let native := Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs
  let oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64) := fun _ => (cfg,[],[])
  let backend := fullInitMachineContext_of_labInit stackConf dataConf maxHeap sp offset native.1 native.2.2.2
    saveRegs dataSp oracle mc ms ffi code code2 labs labelClock i cbspace labClock t m dm sdm labOracle
    newFfiNames shmemInfo newShmemInfo hmc guards stackInit
  refine ⟨_,backend,rfl,List.prefix_refl _,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact labInit_constructed_source_wordMemory stackConf dataConf maxHeap sp offset native.1 native.2.2.2
    saveRegs dataSp oracle mc ms ffi code code2 labs labelClock i cbspace labClock t m dm sdm labOracle
    newFfiNames shmemInfo newShmemInfo hmc guards stackInit template

end SteppedFlapjack.PanToCrepSteps
