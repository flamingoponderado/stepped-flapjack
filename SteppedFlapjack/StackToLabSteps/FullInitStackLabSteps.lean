import SteppedFlapjack.StackToLabSteps.FullInitAllocSteps
import SteppedFlapjack.StackRawCallSteps.EntrySteps
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- The actual full stack initialization compiles a bounded entry run to LabSem
with a computed bound, under the original compiler initialization assumptions. -/
theorem fullInitStackLabWithin {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hwidth : 8 ≤ width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle) :
    let source := (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
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
            computedRunCost offset (uniformFactor (width := width) dataConf * n)
              (.call none (.inl BvlToBvi.initGlobalsLocation) none) base * (uniformFactor (width := width) dataConf * n) + 4),
        ∃ labPost, LabSem.evaluate {lab with clock := m} = (.halt outcome, labPost) ∧
          labPost.ffi.ioEvents = post.ffi.ioEvents := by
  dsimp only
  intro k n res post outcome run nonError hsteps hres
  let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  let source := StackAlloc.makeInit dataConf (sptFromAList code) coracle base
  have codeEq : source.code = sptFromAList code := rfl
  have hdistinct : (code.map Prod.fst).Nodup := hA.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  obtain ⟨rawClock, rawPost, rawRun, rawFfi, rawCost⟩ :=
    SteppedFlapjack.StackRawCallSteps.entryWithinSteps code source BvlToBvi.initGlobalsLocation k res post
      hdistinct codeEq run nonError
  have rawRun' : evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle base with clock := k + rawClock}) =
      (res, rawPost) := by simpa [source, StackAlloc.makeInit] using rawRun
  have rawCost' : steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
      {StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle base with clock := k + rawClock}) ≤ n := by
    apply rawCost.trans hsteps
  obtain ⟨allocClock, allocPost, allocRun, allocFfi, allocCost⟩ :=
    fullInitAllocEntryWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
      hwidth hA (k + rawClock) n res rawPost rawRun' nonError rawCost'
  obtain ⟨m, hm, labPost, labRun, events⟩ :=
    fullInitRemoveLabWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle hA
      (k + rawClock + allocClock) (uniformFactor (width := width) dataConf * n) res allocPost outcome
      allocRun nonError allocCost hres
  refine ⟨m, hm, labPost, labRun, ?_⟩
  rw [events, allocFfi, rawFfi]
end SteppedFlapjack.StackToLabSteps
