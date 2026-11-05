import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.LabToTargetSteps

/-- A bounded entry run from the actual full stack initializer produces a
bounded RISC-V run with the same outcome and I/O events. -/
theorem fullInitStackRiscVWithin {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (p : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc, labCode, labs, p) lab asm machine) :
    let source := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    ∀ (k n : Nat) (res : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (outcome : HolOutcome),
      evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64), {source with clock := k}) = (res, post) →
      res ≠ some .error →
      steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64), {source with clock := k}) ≤ n →
      stackEntryClass res = .CompleteResult outcome →
      ∃ ticks finalMachine finalFfi,
        ticks ≤ labTickBound 4 labCode lab.codeBuffer * (flattenStepFactor *
          (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
            computedRunCost offset (uniformFactor (width := 64) dataConf * n)
              (.call none (.inl BvlToBvi.initGlobalsLocation) none) base * (uniformFactor (width := 64) dataConf * n) + 4)) ∧
        evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome, finalMachine, finalFfi) ∧
        finalFfi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  intro k n res post outcome run nonError hsteps hres
  obtain ⟨m, hm, labPost, labRun, events⟩ :=
    fullInitStackLabWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
      (by decide) hA k n res post outcome run nonError hsteps hres
  obtain ⟨ticks, finalMachine, hbound, machineRun⟩ :=
    labToRiscVWithin p lab labPost outcome m _ mc labCode labs asm machine hmc tie machineRel labRun hm
  exact ⟨ticks, finalMachine, labPost.ffi, hbound, machineRun, events⟩
end SteppedFlapjack.StackToLabSteps
