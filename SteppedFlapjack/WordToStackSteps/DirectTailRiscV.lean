import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.DirectTailLocal

/-! Direct tail-entry execution through the actual RISC-V backend. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps

/-- A completed direct-tail entry yields a bounded RISC-V run using only the
code shape of its syntactic direct callees. -/
theorem allocatedRegTailRiscVWithin {F : Type}
    (ac : AsmConfigExact 64) (program : WordLangProgHOL (BitVec 64)) (shape : SteppedFlapjack.WordAllocSteps.RegTailShape program)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordResult : Option (WordSemResult 64)) (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
    (noInstall : noInstallSubprogsHOL program = true) (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : RegTailLocalCode program word.code)
    (complete : CompleteWordResult wordResult) (notTimeout : wordResult ≠ some .timeOut)
    (stepBound : WordSteps.steps program word ≤ limit)
    (wordPremises : WordSemStateFiniteExact.evaluate program word = (wordResult,wordPost) ∧
      wordResult ≠ some .error ∧ stateRel ac k frameSize frame word {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false program (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k)
    (frameDef : frame = max (maxVarHOL program / 2 + 1 - k) (argumentCount-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize - (argumentCount-k) ≤ entry.stackSpace)
    (found : sptLookup start entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false program argumentCount k (bs,n)).1)
    (inputCode : List (Nat × HolProg 64))
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : entry.code = sptFromAList inputCode)
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F) (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      stackEntryClass stackResult = .CompleteResult outcome ∧
      compCorrectResult ac k frameSize frame {word with clock := limit}
        {wordPost with clock := limit - (word.clock - wordPost.clock)} stackPost wordResult stackResult lens := by
  obtain ⟨stackPost,stackResult,bodyRun,bodyRelation,bodyBound⟩ :=
    regTail_bounded_local ac program shape word wordPost {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} wordResult k frameSize frame bs bsPost n nPost limit
      compiled lens noInstall noInstallCode wordCode notTimeout stepBound wordPremises
  obtain ⟨outcome,classification⟩ := completeWordResult_target ac k frameSize frame _ _ stackPost wordResult stackResult lens complete bodyRelation
  have enabled : entry.useStack = true := wordPremises.2.2.1.2.2.2.2.1
  have foundBody : sptLookup start entry.code = some (.seq (.stackAlloc (frameSize - (argumentCount-k))) compiled) := by
    have compilation := wordPremises.2.2.2.2.2.1
    simp only [Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative, ← frameDef, ← frameSizeDef, compilation] at found
    exact found
  obtain ⟨entryRun,entryNonError,entryBound⟩ := allocatedBody_entry entry start limit (frameSize - (argumentCount-k)) compiled stackResult stackPost outcome _ foundBody enabled space bodyRun classification bodyBound
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
    stackPipelineRiscVWithin inputCode entry start (limit+1) (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))
      stackResult stackPost anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab outcome
      pc mc labCode labs asm machine distinct sourceCode entryRun entryNonError entryBound pre relation ha hs hk hf hcode hor rel hpc classification hmc tie machineRel
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,bodyRelation⟩

end SteppedFlapjack.WordToStackSteps
