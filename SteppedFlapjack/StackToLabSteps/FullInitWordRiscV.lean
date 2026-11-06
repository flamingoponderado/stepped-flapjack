import SteppedFlapjack.StackToLabSteps.FullInitRiscVSteps
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.DirectTailLocal

/-! Connect bounded Word execution to the actual full initialization route. -/
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordToStackSteps

/-- A bounded complete Word call sequence and the actual full Stack
initializer yield a bounded RISC-V run with the related Stack result. -/
theorem fullInitAllocatedWordSequenceRiscVWithin {F : Type}
    (ac : AsmConfigExact 64) (program : WordLangProgHOL (BitVec 64)) (shape : CallSequence program)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordResult : Option (WordSemResult 64)) (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (argumentCount : Nat)
    (noInstall : noInstallSubprogsHOL program = true) (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
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
    (found : sptLookup firstLoopName entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false program argumentCount k (bs,n)).1)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64)) (code : List (Nat × HolProg 64))
    (lab : LabSem.State 64 LabToTarget.Config F) (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (entryEq : entry = (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    let bodyCost := callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F) (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer * (flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
          computedRunCost offset (uniformFactor (width := 64) dataConf * (3+bodyCost))
            (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * (3+bodyCost)) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      stackEntryClass stackResult = .CompleteResult outcome ∧
      compCorrectResult ac k frameSize frame {word with clock := limit}
        {wordPost with clock := limit-(word.clock-wordPost.clock)} stackPost wordResult stackResult lens := by
  obtain ⟨stackPost,stackResult,bodyRun,bodyRelation,bodyBound⟩ :=
    callSequence_bounded ac program shape word wordPost
      {entry with stackSpace := entry.stackSpace-(frameSize-(argumentCount-k))} wordResult
      k frameSize frame bs bsPost n nPost limit compiled lens noInstall noInstallCode wordCode notTimeout stepBound wordPremises
  obtain ⟨outcome,classification⟩ := completeWordResult_target ac k frameSize frame _ _ stackPost wordResult stackResult lens complete bodyRelation
  have enabled : entry.useStack = true := wordPremises.2.2.1.2.2.2.2.1
  have foundBody : sptLookup firstLoopName entry.code = some (.seq (.stackAlloc (frameSize-(argumentCount-k))) compiled) := by
    have compilation := wordPremises.2.2.2.2.2.1
    simp only [Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative,← frameDef,← frameSizeDef,compilation] at found
    exact found
  have full := fullInitAllocatedBodyRiscVWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
    hA pc mc labCode labs asm machine hmc tie machineRel limit (frameSize-(argumentCount-k))
    (callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)) compiled stackResult stackPost outcome
  have result := full (by simpa only [← entryEq] using foundBody) (by simpa only [← entryEq] using enabled)
    (by simpa only [← entryEq] using space) (by simpa only [← entryEq] using bodyRun) classification
    (by simpa only [← entryEq] using bodyBound)
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ := result
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,bodyRelation⟩

/-- The full-initialization bound for the direct-tail Word fragment generated
by the supported Loop entry. -/
theorem fullInitAllocatedRegTailRiscVWithin {F : Type}
    (ac : AsmConfigExact 64) (program : WordLangProgHOL (BitVec 64)) (shape : SteppedFlapjack.WordAllocSteps.RegTailShape program)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordResult : Option (WordSemResult 64)) (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (argumentCount : Nat)
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
    (found : sptLookup firstLoopName entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false program argumentCount k (bs,n)).1)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64)) (code : List (Nat × HolProg 64))
    (lab : LabSem.State 64 LabToTarget.Config F) (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle)
    (entryEq : entry = (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle).1)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    let bodyCost := callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F) (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer * (flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
          computedRunCost offset (uniformFactor (width := 64) dataConf * (3+bodyCost))
            (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * (3+bodyCost)) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      stackEntryClass stackResult = .CompleteResult outcome ∧
      compCorrectResult ac k frameSize frame {word with clock := limit}
        {wordPost with clock := limit-(word.clock-wordPost.clock)} stackPost wordResult stackResult lens := by
  obtain ⟨stackPost,stackResult,bodyRun,bodyRelation,bodyBound⟩ :=
    regTail_bounded_local ac program shape word wordPost
      {entry with stackSpace := entry.stackSpace-(frameSize-(argumentCount-k))} wordResult
      k frameSize frame bs bsPost n nPost limit compiled lens noInstall noInstallCode wordCode notTimeout stepBound wordPremises
  obtain ⟨outcome,classification⟩ := completeWordResult_target ac k frameSize frame _ _ stackPost wordResult stackResult lens complete bodyRelation
  have enabled : entry.useStack = true := wordPremises.2.2.1.2.2.2.2.1
  have foundBody : sptLookup firstLoopName entry.code = some (.seq (.stackAlloc (frameSize-(argumentCount-k))) compiled) := by
    have compilation := wordPremises.2.2.2.2.2.1
    simp only [Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative,← frameDef,← frameSizeDef,compilation] at found
    exact found
  have full := fullInitAllocatedBodyRiscVWithin stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle
    hA pc mc labCode labs asm machine hmc tie machineRel limit (frameSize-(argumentCount-k))
    (callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)) compiled stackResult stackPost outcome
  have result := full (by simpa only [← entryEq] using foundBody) (by simpa only [← entryEq] using enabled)
    (by simpa only [← entryEq] using space) (by simpa only [← entryEq] using bodyRun) classification
    (by simpa only [← entryEq] using bodyBound)
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ := result
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,bodyRelation⟩

end SteppedFlapjack.StackToLabSteps
