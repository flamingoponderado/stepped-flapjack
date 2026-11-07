import SteppedFlapjack.PanToCrepSteps.CountdownBackendConfig
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyWordToStack

/-! Derive Stack initialization from the original compiler's memory layout. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang Flapjack.Pancake.Proofs.PanToTarget

/-- The concrete register and memory layout used by the original full initializer. -/
def countdownStackMemoryLayout
    (config : Backend.Config) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (machine : RiscV.L3.riscv_state) (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64)
    (bitmapPtr : BitVec 64) (bitmapsDomain : BitVec 64 → Bool) (bytes : List (BitVec 8))
    (cbspace dataSp : Nat) (bitmaps : List (BitVec 64)) : Prop :=
  let r1 := StackNames.findNameSpt config.stackConf.regNames 2
  let r2 := StackNames.findNameSpt config.stackConf.regNames 4
  let biw := StackRemove.bytesInWord 64
  let heapDomain : BitVec 64 → Bool := fun w => decide (asm.regs r1 ≤ w ∧ w < asm.regs r2)
  holByteAligned (asm.regs r1) = true ∧ holByteAligned (asm.regs r2) = true ∧
  holByteAligned bitmapPtr = true ∧ asm.regs r1 ≤ asm.regs r2 ∧
  1024 * biw ≤ asm.regs r2 - asm.regs r1 ∧
  (∀ w, ¬ (heapDomain w = true ∧ bitmapsDomain w = true)) ∧
  memory (asm.regs r1) = .word bitmapPtr ∧
  memory (asm.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat 64 bitmaps.length) ∧
  memory (asm.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat 64 dataSp + biw * BitVec.ofNat 64 bitmaps.length) ∧
  memory (asm.regs r1 + 3 * biw) = .word (mc.target.getPc machine + BitVec.ofNat 64 bytes.length) ∧
  memory (asm.regs r1 + 4 * biw) = .word (mc.target.getPc machine + BitVec.ofNat 64 cbspace + BitVec.ofNat 64 bytes.length) ∧
  SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
    (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat 64 bitmaps.length) dataSp)
    (SetSep.fun2Set (memory, fun a => holByteAligned a = true ∧ bitmapsDomain a = true))

/-- Lab code obtained from the actual native countdown output. -/
noncomputable def countdownStackLabCode (name : MlString) (initial returned : BitVec 64) (config : Backend.Config) :
    LabSem.LabProgHOL 64 :=
  StackToLab.compile config.stackConf config.dataConf (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
    (countdownNativeRiscV name initial returned config.wordToWordConf).2.2.2

/-- Aligned heap and bitmap cells used by the original initializer. -/
noncomputable def countdownStackLabDomain (config : Backend.Config) (asm : AsmState 64)
    (bitmapsDomain : BitVec 64 → Bool) : BitVec 64 → Bool :=
  fun a => (decide (asm.regs (StackNames.findNameSpt config.stackConf.regNames 2) ≤ a ∧
    a < asm.regs (StackNames.findNameSpt config.stackConf.regNames 4)) || bitmapsDomain a) && holByteAligned a

/-- The Lab oracle corresponding to a no-install Stack oracle. -/
def countdownStackLabOracle (config : Backend.Config) (cfg : Config) : Nat → Config × LabSem.LabProgHOL 64 :=
  fun _ => (cfg,StackToLab.compileNoStubs config.stackConf.regNames config.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])

/-- The compiled countdown and the original memory-layout conditions imply
the full Stack-to-Lab initializer relation. -/
theorem countdown_stackInit_from_memory {σ : Type}
    (name : MlString) (initial returned : BitVec 64) (config : Backend.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ) (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64)
    (bitmapPtr : BitVec 64) (bitmapsDomain sharedDomain : BitVec 64 → Bool)
    (bytes : List (BitVec 8)) (cbspace dataSp : Nat) (cfg : Config)
    (comp : Config → LabSem.LabProgHOL 64 → Option (List (BitVec 8) × Config))
    (target : mc.target = riscvTarget) (hcfg : backendConfigOk riscvConfig config)
    (hinit : mcInitOk riscvConfig config mc)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11) (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13)
    (layout : countdownStackMemoryLayout config mc machine asm memory bitmapPtr bitmapsDomain bytes cbspace dataSp
      (countdownNativeRiscV name initial returned config.wordToWordConf).1) :
    let native := countdownNativeRiscV name initial returned config.wordToWordConf
    let sp := riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 config.dataConf - 1
    let r1 := StackNames.findNameSpt config.stackConf.regNames 2
    let r2 := StackNames.findNameSpt config.stackConf.regNames 4
    let heapDomain : BitVec 64 → Bool := fun w => decide (asm.regs r1 ≤ w ∧ w < asm.regs r2)
    let code := StackToLab.compile config.stackConf config.dataConf maxHeap sp riscvConfig.addrOffset native.2.2.2
    let oracle : Nat → Config × LabSem.LabProgHOL 64 := fun _ => (cfg,StackToLab.compileNoStubs config.stackConf.regNames config.stackConf.jump riscvConfig.addrOffset sp [])
    let lab := LabToTarget.makeInit mc ffi asm memory
      (fun a => (heapDomain a || bitmapsDomain a) && holByteAligned a)
      (fun a => sharedDomain a && holByteAligned a) machine code comp
      (mc.target.getPc machine + BitVec.ofNat 64 bytes.length) cbspace oracle
    StackToLab.Proofs.FullMakeInitSemantics.Assumptions config.stackConf config.dataConf maxHeap sp riscvConfig.addrOffset
      native.1 native.2.2.2 lab (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (cfg,[],[])) := by
  let source := singleEntryProgram (ofString "main")
    (.dec name .one (.const initial) (.seq .skip (.seq
      (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
      (.return (.const returned)))))
  let word := WordToWord.compile config.wordToWordConf riscvConfig (panToWordCompileProgHOL riscvConfig.isa source)
  let native := WordToStack.Native.compileNative riscvConfig false word.2
  have h := panToTargetFullMakeInitAssumptions config mc ffi asm memory bitmapPtr bitmapsDomain sharedDomain machine
    comp bytes cbspace cfg source word.1 word.2 native.1 native.2.1 native.2.2.1 native.2.2.2 dataSp
    (by rw [target]; exact hcfg) (riscvTarget_mcConfOk mc target ptr len ptr2 len2)
    (by rw [target]; exact hinit) (by simp [target,riscvTarget,riscvConfig])
    (by rw [target]; exact Prod.mk.eta.symm)
    (by rw [target]; simp only [Prod.mk.eta]; rfl)
    (by simp [source,singleEntryProgram,functionsHOL])
  have memoryFacts : countdownStackMemoryLayout config mc machine asm memory bitmapPtr bitmapsDomain bytes cbspace dataSp native.1 := by
    simpa only [native,word,source,countdownNativeRiscV] using layout
  have result := h (by simpa only [countdownStackMemoryLayout] using memoryFacts)
  simpa only [target,riscvTarget,native,word,source,countdownNativeRiscV] using result

end SteppedFlapjack.PanToCrepSteps
