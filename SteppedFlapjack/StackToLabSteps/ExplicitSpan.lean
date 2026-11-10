import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.StackRemoveSteps.ExplicitFields
import Flapjack.Compiler.Backend.LabProps.EvaluateAddClock
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemEvaluate
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
end SteppedFlapjack.StackToLabSteps
