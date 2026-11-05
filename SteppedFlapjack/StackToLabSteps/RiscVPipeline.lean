import SteppedFlapjack.StackToLabSteps.PipelineComposition
import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.LabToTargetSteps

/-- A bounded StackSem entry run is simulated through the completed backend
passes by a RISC-V run with a computed target-step bound. -/
theorem stackPipelineRiscVWithin {F : Type}
    (inputCode : List (Nat × HolProg 64)) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (start clock n : Nat) (result : Option (StackSemResult 64)) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (lab : Flapjack.Compiler.Backend.LabSem.State 64 LabToTarget.Config F) (outcome : HolOutcome)
    (p : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList inputCode)
    (run : evaluate ((.call none (.inl start) none : HolProg 64), {source with clock := clock}) = (result, post))
    (nonError : result ≠ some .error)
    (sourceSteps : steps ((.call none (.inl start) none : HolProg 64), {source with clock := clock}) ≤ n)
    (pre : Pre cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} source.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} 0 source.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (hres : stackEntryClass result = .CompleteResult outcome)
    (hmc : mc.target = riscvTarget)
    (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc, labCode, labs, p) lab asm machine) :
    ∃ ticks finalMachine finalFfi,
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor *
          (computedRunCost bounds (uniformFactor (width := 64) c * n) (.call none (.inl start) none)
            (Tgt anything cr c {source with code := sptFromAList (StackRawCall.compile inputCode), clock := clock} 0 source.regs) *
            (uniformFactor (width := 64) c * n) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome, finalMachine, finalFfi) ∧
      finalFfi.ioEvents = post.ffi.ioEvents := by
  obtain ⟨m, mBound, labPost, labRun, events⟩ :=
    stackPipelineLabWithin inputCode source start clock n result post anything cr c (by decide)
      jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab outcome
      distinct sourceCode run nonError sourceSteps pre relation ha hs hk hf hcode hor rel hpc hres
  obtain ⟨ticks, finalMachine, ticksBound, machineRun⟩ :=
    labToRiscVWithin p lab labPost outcome m _ mc labCode labs asm machine hmc tie machineRel labRun mBound
  exact ⟨ticks, finalMachine, labPost.ffi, ticksBound, machineRun, events⟩
end SteppedFlapjack.StackAllocSteps
