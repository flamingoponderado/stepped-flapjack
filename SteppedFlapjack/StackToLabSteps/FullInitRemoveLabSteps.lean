import SteppedFlapjack.StackRemoveSteps.InitHypSteps
import SteppedFlapjack.StackToLabSteps.FullInitLabSteps
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- Actual stack-removal initialization and Lab flattening preserve an entry
run within a computable bound under the compiler's initialization assumptions. -/
theorem fullInitRemoveLabWithin {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle) :
    let source := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    ∀ (k n : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
      (outcome : HolOutcome),
    evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {source with clock := k}) = (res, post) →
    res ≠ some .error →
    steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {source with clock := k}) ≤ n →
    stackEntryClass res = .CompleteResult outcome →
    ∃ m ≤ flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg width) +
          computedRunCost offset n (.call none (.inl BvlToBvi.initGlobalsLocation) none) source * n + 4),
      ∃ labPost, LabSem.evaluate {lab with clock := m} = (.halt outcome, labPost) ∧
        labPost.ffi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  intro k n res post outcome run nonError hsteps hres
  let target := s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle
  let source := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code)) target
  have bundles : InitMake.dischargeThese stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
      maxHeap sp BvlToBvi.initGlobalsLocation (coracle1 coracle) (code1 dataConf code) target ∧
      InitMake.propagateThese target bitmaps dataSp := ⟨dischargeThese_s2 hA, propagateThese_s2 hA⟩
  have hyp := initHypOfBundles stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
    maxHeap sp BvlToBvi.initGlobalsLocation (coracle1 coracle) (code1 dataConf code) target bitmaps dataSp bundles
  obtain ⟨initialized, opt, _⟩ := InitSemantics.makeInitSemantics stackConf.jump offset
    (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (coracle1 coracle) (code1 dataConf code) target bitmaps dataSp bundles
  have sourceEq : source = initialized := by
    simp [source, InitMake.makeInitAny, opt]
  have opt' : InitMake.makeInitOpt (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code)) target = some source := by
    rw [sourceEq]
    exact opt
  obtain ⟨extra, targetPost, targetRun, targetFfi, targetSteps⟩ :=
    initEntryWithinSteps (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp sp
      BvlToBvi.initGlobalsLocation target source stackConf.jump offset (coracle1 coracle)
      (sptFromAList (code1 dataConf code)) hyp opt' k n res post run nonError hsteps
  obtain ⟨m, hm, labPost, labRun, events⟩ :=
    fullInitLabStageWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
      (extra + k + 1) _ res targetPost outcome hA targetRun targetSteps hres
  exact ⟨m, hm, labPost, labRun, events.trans (congrArg _ targetFfi)⟩
end SteppedFlapjack.StackToLabSteps
