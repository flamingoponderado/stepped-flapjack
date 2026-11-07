import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.LabToTargetSteps.FilteredRiscV
import SteppedFlapjack.StackToLabSteps.EntryLocation
import SteppedFlapjack.WordToStackSteps.EntryComposition
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.LabToTargetSteps

/-- A bounded run at the first compiled Pancake function from the actual full
stack initializer and skip-filtered Lab program produce a bounded RISC-V run with the same outcome and
I/O events. The backend initialization entry is this same location. -/
theorem fullInitStackFilteredRiscVWithin {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab machineLab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (p : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (filterRel : LabFilter.Proofs.stateRel machineLab lab)
    (tie : LabToTarget.oracleTie mc machine machineLab)
    (machineRel : LabToTarget.stateRel (mc, labCode, labs, p) machineLab asm machine) :
    let source := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    ∀ (k n : Nat) (res : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (outcome : HolOutcome),
      evaluate ((.call none (.inl firstLoopName) none : HolProg 64), {source with clock := k}) = (res, post) →
      res ≠ some .error →
      steps ((.call none (.inl firstLoopName) none : HolProg 64), {source with clock := k}) ≤ n →
      stackEntryClass res = .CompleteResult outcome →
      ∃ ticks finalMachine finalFfi,
        ticks ≤ labTickBound 4 labCode machineLab.codeBuffer * (flattenStepFactor *
          (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
            computedRunCost offset (uniformFactor (width := 64) dataConf * n)
              (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * n) + 4)) ∧
        evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome, finalMachine, finalFfi) ∧
        finalFfi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  intro k n res post outcome run nonError hsteps hres
  obtain ⟨m, hm, labPost, labRun, events⟩ :=
    fullInitStackLabWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
      (by decide) hA k n res post outcome run nonError hsteps hres
  obtain ⟨ticks, finalMachine, hbound, machineRun⟩ :=
    unfilteredLabToRiscVWithin p machineLab lab labPost outcome m _ mc labCode labs asm machine
      hmc filterRel tie machineRel labRun hm
  exact ⟨ticks, finalMachine, labPost.ffi, hbound, machineRun, events⟩

/-- A bounded compiled function body at the Pancake entry runs through the
actual full Stack initializer and RISC-V pipeline. The entry-call and stack
allocation overhead are derived from the body run. -/
theorem fullInitAllocatedBodyFilteredRiscVWithin {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab machineLab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (p : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (filterRel : LabFilter.Proofs.stateRel machineLab lab)
    (tie : LabToTarget.oracleTie mc machine machineLab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,p) machineLab asm machine)
    (limit allocation bound : Nat) (body : HolProg 64) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config F) (outcome : HolOutcome) :
    let source := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    sptLookup firstLoopName source.code = some (.seq (.stackAlloc allocation) body) →
    source.useStack = true → allocation ≤ source.stackSpace →
    evaluate (body,{source with stackSpace := source.stackSpace-allocation,clock := limit}) = (result,post) →
    stackEntryClass result = .CompleteResult outcome →
    SteppedFlapjack.StackSteps.steps (body,{source with stackSpace := source.stackSpace-allocation,clock := limit}) ≤ bound →
    ∃ ticks finalMachine finalFfi,
      ticks ≤ labTickBound 4 labCode machineLab.codeBuffer * (flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
          computedRunCost offset (uniformFactor (width := 64) dataConf * (3+bound))
            (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * (3+bound)) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  intro found enabled space run complete cost
  obtain ⟨entryRun,nonError,entryCost⟩ := SteppedFlapjack.WordToStackSteps.allocatedBody_entry
    (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    firstLoopName limit allocation body result post outcome bound found enabled space run complete cost
  exact fullInitStackFilteredRiscVWithin stackConf dataConf maxHeap sp offset bitmaps code lab machineLab saveRegs dataSp coracle
    hA p mc labCode labs asm machine hmc filterRel tie machineRel (limit+1) (3+bound) result post outcome
    entryRun nonError entryCost complete


/-- If the compiled entry cannot allocate its stack frame, the actual full
initializer reaches the corresponding bounded RISC-V resource outcome. -/
theorem fullInitAllocationFailureFilteredRiscVWithin {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab machineLab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (p : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (filterRel : LabFilter.Proofs.stateRel machineLab lab)
    (tie : LabToTarget.oracleTie mc machine machineLab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,p) machineLab asm machine)
    (limit allocation : Nat) (body : HolProg 64) :
    let source := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    sptLookup firstLoopName source.code = some (.seq (.stackAlloc allocation) body) →
    source.useStack = true → source.stackSpace < allocation →
    ∃ ticks finalMachine finalFfi,
      ticks ≤ labTickBound 4 labCode machineLab.codeBuffer * (flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
          computedRunCost offset (uniformFactor (width := 64) dataConf * 3)
            (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * 3) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt .resourceLimitHit,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = source.ffi.ioEvents := by
  dsimp only
  intro found enabled space
  obtain ⟨post,run,complete,ffi,cost⟩ := SteppedFlapjack.WordToStackSteps.allocationFailure_entry
    (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    firstLoopName limit allocation body found enabled space
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
    fullInitStackFilteredRiscVWithin stackConf dataConf maxHeap sp offset bitmaps code lab machineLab saveRegs dataSp coracle
      hA p mc labCode labs asm machine hmc filterRel tie machineRel (limit+1) 3 (some (.halt (.word 2))) post
      .resourceLimitHit run (by simp) cost complete
  exact ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events.trans (congrArg _ ffi)⟩

end SteppedFlapjack.StackToLabSteps
