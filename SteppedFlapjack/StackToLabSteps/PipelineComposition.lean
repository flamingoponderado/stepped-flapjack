import SteppedFlapjack.StackAllocSteps.ThreePassComposition
import SteppedFlapjack.StackToLabSteps.NamesComposition
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackToLabSteps

/-- A source StackSem entry bound transported through raw-call optimization,
allocation, stack removal, renaming and flattening to a LabSem clock bound. -/
theorem stackPipelineLabWithin {width : Nat} [NeZero width] {C F : Type}
    (inputCode : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock n : Nat) (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (anything : WordSemGcFun width) (cr : CompileFn width C) (c : Config) (hwidth : 8 ≤ width)
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (renamed : StackSemStateFiniteExact width C F) (lab : Flapjack.Compiler.Backend.LabSem.State width C F)
    (outcome : HolOutcome)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList inputCode)
    (run : evaluate ((.call none (.inl start) none : HolProg width), {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (sourceSteps : steps ((.call none (.inl start) none : HolProg width), {source with clock := clock}) ≤ n)
    (pre : Pre cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} source.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} 0 source.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : Flapjack.Compiler.Backend.LabSem.locToPc start 0 lab.code = some lab.pc)
    (hres : stackEntryClass result = .CompleteResult outcome) :
    ∃ m ≤ flattenStepFactor *
        (computedRunCost bounds (uniformFactor (width := width) c * n) (.call none (.inl start) none)
          (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} 0 source.regs) *
          (uniformFactor (width := width) c * n) + 4),
      ∃ labPost, Flapjack.Compiler.Backend.LabSem.evaluate {lab with clock := m} = (.halt outcome, labPost) ∧
        labPost.ffi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨rawClock, allocClock, removeClock, removePost, removeRun, removeFfi, removeCost⟩ :=
    threePassEntryWithinSteps inputCode source
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed)
      start clock n result post anything cr c hwidth jump bounds pointer distinct sourceCode run nonError sourceSteps pre relation
  obtain ⟨m, hm, labPost, labRun, labFfi⟩ :=
    namesFlattenGeneratedWithin f jump bounds gen maxHeap a b removeInput oracle renamed lab start
      (removeClock + (clock + rawClock + allocClock)) _ result removePost outcome
      ha hs hk hf hcode hor rel hpc removeRun removeCost hres
  refine ⟨m, hm, labPost, labRun, ?_⟩
  rw [labFfi, removeFfi]
end SteppedFlapjack.StackAllocSteps
