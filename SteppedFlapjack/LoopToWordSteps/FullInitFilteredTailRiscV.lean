import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV
import SteppedFlapjack.StackToLabSteps.FullInitFilteredWordRiscV

/-! Bounded Loop execution through the full initialized backend. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps

/-- A bounded supported Loop entry gives a RISC-V bound through the actual
full Stack initializer, with success and resource outcomes. -/
theorem singleTail_fullInit_filtered_riscvWithin {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (ac : AsmConfigExact 64) (count name alg regCount : Nat) (col : Option (Spt Nat))
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (compiledCode : Spt (Nat × WordLangProgHOL (BitVec 64))) (locals : Spt (WordLocW 64)) (limit : Nat)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (complete : CompleteLoopResult result) (gc : gcFunConstOk word.gcFun)
    (noInstall : WordProps.noInstallCode word.code) (codeRel : codeRel word.code compiledCode)
    (codeDomain : sptDomain word.code = sptDomain compiledCode)
    (localsRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) (sourceBound : LoopSteps.steps p source ≤ limit)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F) (frameSize frame : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64) (argumentCount : Nat)
    (stackRel : stateRel ac regCount frameSize frame
      {word with code := compiledCode,locals := locals,clock := tailWordReplayLimit p ctxt labels compiledCode limit}
      {entry with stackSpace := entry.stackSpace-(frameSize-(argumentCount-regCount))} lens 0)
    (native : Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
      (bs,n) (regCount,frameSize,frame) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n) (bitmapBound : n-(appListAppend bs).length ≤ entry.bitmaps.length)
    (bitmapPrefix : List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)))
    (labelCheck : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc)
    (maxBound : maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 < 2*frame+2*regCount)
    (frameDef : frame = max (maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 / 2 + 1 - regCount) (argumentCount-regCount))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize-(argumentCount-regCount) ≤ entry.stackSpace)
    (found : sptLookup firstLoopName entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 argumentCount regCount (bs,n)).1)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64)) (inputCode : List (Nat × HolProg 64))
    (lab machineLab : LabSem.State 64 LabToTarget.Config F) (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp coracle)
    (entryEq : entry = {(fullMakeInit stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp coracle).1 with clock := entry.clock})
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget) (filterRel : LabExecutionLink machineLab lab)
    (tie : LabToTarget.oracleTie mc machine machineLab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) machineLab asm machine) :
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
    let stackLimit := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf inputCode))
      (s2 stackConf dataConf maxHeap sp offset inputCode lab saveRegs coracle)
    let cost := 3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame)
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F)
      (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode machineLab.codeBuffer * (flattenStepFactor *
        (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp : HolProg 64) +
          computedRunCost offset (uniformFactor (width := 64) dataConf * cost)
            (.call none (.inl firstLoopName) none) base * (uniformFactor (width := 64) dataConf * cost) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧ stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ wordPost wordResult perm selectedLocals targetPost,
        LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
        wordPost.ffi = sourcePost.ffi ∧
        wordStateEqRel {wordPost with code := compiledCode,permute := perm,locals := selectedLocals,clock := tailWordReplayLimit p ctxt labels compiledCode limit-(6*limit-(6*limit-(word.clock-wordPost.clock)))} targetPost ∧
        compCorrectResult ac regCount frameSize frame
          {word with code := compiledCode,locals := locals,clock := stackLimit}
          {targetPost with clock := stackLimit-(tailWordReplayLimit p ctxt labels compiledCode limit-targetPost.clock)}
          stackPost wordResult stackResult lens ∧
        ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents ∧
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) ∧
        WordSemStateFiniteExact.evaluate out
          {word with code := compiledCode,locals := locals,clock := tailWordReplayLimit p ctxt labels compiledCode limit} =
          (wordResult,targetPost) := by
  obtain ⟨outShape,localCode,outNoInstall,outFlat,outConvention,wordPost,wordResult,perm,selectedLocals,targetPost,
    wordRel,wordFfi,targetRel,targetRun,targetBound⟩ :=
    singleTail_compiledCode_word_bound ac count name alg regCount col shape calleeShape source sourcePost result
      word ctxt labels compiledCode locals limit lookup premises complete gc noInstall codeRel codeDomain localsRel domain sourceBound
  obtain ⟨wordComplete,_,wordNotTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have compiledNoInstall := Flapjack.Compiler.Backend.WordToWord.noInstallCode_of_codeRel word.code compiledCode codeRel codeDomain noInstall
  have notError : wordResult ≠ some .error := by cases wordComplete <;> simp
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,stackRelation⟩ :=
    fullInitAllocatedRegTailFilteredRiscVWithin ac _ outShape
      {word with code := compiledCode,locals := locals,clock := tailWordReplayLimit p ctxt labels compiledCode limit}
      targetPost wordResult entry regCount frameSize frame
      (tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit) lens bs bsPost n nPost
      compiled argumentCount outNoInstall compiledNoInstall localCode wordComplete wordNotTimeout
      (by simpa [tailWordReplayLimit,tailStackReplayLimit] using targetBound)
      ⟨by simpa [tailWordReplayLimit] using targetRun,notError,stackRel,outConvention,outFlat,native,lengthBound,bitmapBound,bitmapPrefix,labelCheck,maxBound⟩
      frameDef frameSizeDef space found stackConf dataConf maxHeap sp offset bitmaps inputCode lab machineLab saveRegs dataSp coracle
      hA entryEq pc mc labCode labs asm machine hmc filterRel tie machineRel
  have targetFfi : targetPost.ffi = sourcePost.ffi := by
    have h := targetRel
    simp only [wordStateEqRel] at h
    have ffi := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact ffi.trans wordFfi
  have wordOutcome := loopWordOutcome_of_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have correspondence := loopMachine_correspondence ac regCount frameSize frame lens
    {word with code := compiledCode,locals := locals,clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit}
    {targetPost with clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit-
      (tailWordReplayLimit p ctxt labels compiledCode limit-targetPost.clock)}
    sourcePost stackPost result wordResult stackResult outcome finalFfi targetFfi wordOutcome
    stackRelation classification events
  refine ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,
    wordPost,wordResult,perm,selectedLocals,targetPost,wordRel,wordFfi,targetRel,stackRelation,correspondence,?_⟩
  simpa only [tailWordReplayLimit] using targetRun

end SteppedFlapjack.LoopToWordSteps
