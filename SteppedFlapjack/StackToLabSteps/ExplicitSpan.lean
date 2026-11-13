import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.StackRemoveSteps.ExplicitFields
import SteppedFlapjack.StackSteps.TableBound
import SteppedFlapjack.LabToTargetSteps.DomainAlignmentBridge
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- A Stack-to-Lab clock bound computed solely from the compiled input, bitmap
and finite compiler-oracle prefix. -/
def stackLabTickLimit {width : Nat} [NeZero width] {C : Type}
    (dataConf : DataToWord.Config) (maxHeap sp : Nat) (offset : BitVec width × BitVec width)
    (bitmaps : List (BitVec width)) (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) (n : Nat) : Nat :=
  let cost := uniformFactor (width := width) dataConf * n
  let entry := (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width)
  let generated := sptFromAList (code1 dataConf code)
  let oracle1 := coracle1 oracle
  let factor := max (costFromFields offset cost entry generated bitmaps oracle1)
    (costFromFields offset cost entry generated [4] oracle1)
  flattenStepFactor * (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg width) + factor * cost + 4)

/-- With no dynamic installations, the general clock bound has a factor
computed once from the generated code and bitmaps, independent of `n`. -/
theorem stackLabTickLimit_emptyOracle {width : Nat} [NeZero width] {C : Type}
    (dataConf : DataToWord.Config) (maxHeap sp : Nat) (offset : BitVec width × BitVec width)
    (bitmaps : List (BitVec width)) (code : List (Nat × HolProg width)) (cfg : C) (n : Nat) :
    stackLabTickLimit dataConf maxHeap sp offset bitmaps code (fun _ => (cfg,[],[])) n =
      let entry := (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width)
      let generated := sptFromAList (code1 dataConf code)
      let oracle := (fun _ : Nat => (cfg,([] : List (Nat × HolProg width)),([] : List (BitVec width))))
      let factor := max (costFromFields offset 0 entry generated bitmaps oracle)
        (costFromFields offset 0 entry generated [4] oracle)
      flattenStepFactor * (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg width) +
        factor * (uniformFactor (width := width) dataConf * n) + 4) := by
  have oracle : coracle1 (fun _ : Nat => (cfg,([] : List (Nat × HolProg width)),([] : List (BitVec width)))) =
      (fun _ : Nat => (cfg,([] : List (Nat × HolProg width)),([] : List (BitVec width)))) := by funext i; rfl
  unfold stackLabTickLimit
  rw [oracle]
  dsimp only
  simp only [costFromFields_emptyOracle]

/-- A bounded run from the full Stack initializer reaches the matching Lab
outcome and events at an explicit compiler-derived clock. -/
theorem fullInitStackLab_explicit {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hwidth : 8 ≤ width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (k n : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (run : evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) with clock := k}) = (res,post))
    (nonError : res ≠ some .error)
    (bounded : steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) with clock := k}) ≤ n)
    (complete : stackEntryClass res = .CompleteResult outcome) :
    ∃ labPost, LabSem.evaluate {lab with clock := stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n} =
      (.halt outcome,labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨m,hm,labPost,labRun,events⟩ := fullInitStackLabWithin stackConf dataConf maxHeap sp offset
    bitmaps code lab saveRegs dataSp coracle hwidth hA k n res post outcome run nonError bounded complete
  let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have factor := makeInitAny_cost_bounded (StackToLab.isGenGc dataConf.gcKind) stackConf.jump maxHeap bitmaps
    dataSp (coracle1 coracle) offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    (uniformFactor (width := width) dataConf * n) (.call none (.inl BvlToBvi.initGlobalsLocation) none)
  have le : m ≤ stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n := by
    unfold stackLabTickLimit
    dsimp only at hm ⊢
    apply hm.trans
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_right _ factor
  have boosted := LabProps.evaluateAddClock {lab with clock := m} (.halt outcome) labPost
    (stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n - m) ⟨labRun,by simp⟩
  refine ⟨{labPost with clock := labPost.clock + (stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n - m)},?_,events⟩
  simpa only [Nat.add_sub_of_le le] using boosted
/-- With no dynamically installed code, the Stack-to-Lab theorem derives its
visit budget from the concrete initial code and source clock. -/
theorem fullInitStackLab_table_explicit {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (empty : ∀ i, (coracle i).2.1 = [])
    (hwidth : 8 ≤ width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (run : evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) with clock := k}) = (res,post))
    (nonError : res ≠ some .error) (complete : stackEntryClass res = .CompleteResult outcome) :
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * k
    ∃ labPost, LabSem.evaluate {lab with clock := stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n} =
      (.halt outcome,labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  let initial := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
  let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * k
  have initCode : initial.code = sptFromAList code := by
    simp [initial,fullMakeInit,StackAlloc.makeInit]
  have initOracle : emptyCodeOracle {initial with clock := k} := by
    intro i
    simpa [initial,fullMakeInit,StackAlloc.makeInit] using empty i
  have bounded := stackTable_clock_bound (.call none (.inl BvlToBvi.initGlobalsLocation) none)
    {initial with clock := k} initOracle
  have bound : steps (.call none (.inl BvlToBvi.initGlobalsLocation) none, {initial with clock := k}) ≤ n := by
    simpa [stackControlWeight,initCode,n] using bounded
  exact fullInitStackLab_explicit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
    hwidth hA k n res post outcome run nonError bound complete

/-- A complete Stack run reaches RISC-V at a concrete tick limit computed
from its initial code, clock, and compiler configuration. -/
theorem fullInitStackRiscV_table_explicit {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab filtered : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (empty : ∀ i, (coracle i).2.1 = [])
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (outcome : HolOutcome)
    (run : evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
      {((fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1) with clock := k}) = (res,post))
    (nonError : res ≠ some .error) (complete : stackEntryClass res = .CompleteResult outcome)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (link : LabToTargetSteps.LabExecutionLink filtered lab)
    (tie : LabToTarget.oracleTie mc machine filtered) (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * k
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc lab.ffi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n) machine =
          (.halt outcome,finalMachine,finalFfi) ∧ finalFfi.ioEvents = post.ffi.ioEvents := by
  let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * k
  obtain ⟨labPost,labRun,events⟩ := fullInitStackLab_table_explicit stackConf dataConf maxHeap sp offset
    bitmaps code lab saveRegs dataSp coracle empty (by decide) hA k res post outcome run nonError complete
  obtain ⟨finalMachine,machineRun⟩ := LabToTargetSteps.connectedLabToRiscVExplicit pc filtered lab labPost outcome
    (stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n)
    (stackLabTickLimit dataConf maxHeap sp offset bitmaps code coracle n) mc labCode labs asm machine hmc link tie rel labRun (by rfl)
  exact ⟨finalMachine,labPost.ffi,machineRun,events⟩

end SteppedFlapjack.StackToLabSteps
