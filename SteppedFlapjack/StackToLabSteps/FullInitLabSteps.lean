import SteppedFlapjack.StackToLabSteps.NamesComposition
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackSteps

/-- The initialized stack-removal output reaches the actual LabSem state with
a bounded clock and no separate halt-cost or state-relation hypothesis. -/
theorem fullInitLabStageWithin {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (k n : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (run : evaluate ((.call none (.inl 0) none : HolProg width),
      {s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle with clock := k}) = (res, post))
    (hsteps : steps ((.call none (.inl 0) none : HolProg width),
      {s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle with clock := k}) ≤ n)
    (hres : stackEntryClass res = .CompleteResult outcome) :
    ∃ m ≤ flattenStepFactor * (n + 4), ∃ labPost,
      LabSem.evaluate {lab with clock := m} = (.halt outcome, labPost) ∧ labPost.ffi.ioEvents = post.ffi.ioEvents := by
  have hrel := stateRel_s3 hA
  have hpc := locToPc_start hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbij⟩ := hA
  have hcode : (s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle).code =
      sptFromAList (StackNames.compileHOL stackConf.regNames
        (StackRemove.compileHOL stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind) maxHeap sp
          BvlToBvi.initGlobalsLocation (code1 dataConf code))) := rfl
  have hor : (s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle).compileOracle =
      Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘ coracle2 stackConf sp offset coracle := rfl
  have halloc : ¬(s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle).useAlloc := by
    simp [s3, MakeInit.makeInit]
  have hstore : ¬(s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle).useStore := by
    simp [s3, MakeInit.makeInit]
  have hstack : ¬(s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle).useStack := by
    simp [s3, MakeInit.makeInit]
  exact namesFlattenGeneratedWithin stackConf.regNames stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
    maxHeap sp BvlToBvi.initGlobalsLocation (code1 dataConf code) (coracle2 stackConf sp offset coracle)
    (s3 stackConf dataConf maxHeap sp offset code lab saveRegs coracle) lab 0 k n res post outcome
    halloc hstore hstack hbij hcode hor hrel hpc run hsteps hres
end SteppedFlapjack.StackToLabSteps
