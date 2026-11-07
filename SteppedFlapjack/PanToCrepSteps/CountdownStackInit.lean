import SteppedFlapjack.PanToCrepSteps.CountdownGoodCode
import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi
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

/-- The Lab oracle corresponding to a no-install Stack oracle. -/
def countdownStackLabOracle (config : Backend.Config) (cfg : Config) : Nat → Config × LabSem.LabProgHOL 64 :=
  fun _ => (cfg,StackToLab.compileNoStubs config.stackConf.regNames config.stackConf.jump riscvConfig.addrOffset
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])

end SteppedFlapjack.PanToCrepSteps
