import SteppedFlapjack.LoopToWordSteps.TailEntryCompiledCode
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.DirectTailRiscV

/-! Loop tail entries through the actual Word and RISC-V compiler pipeline. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps

/-- Replay clock for an entry after replacing its Word code table. -/
noncomputable def tailWordReplayLimit (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (limit : Nat) : Nat :=
  sizeOf (LoopToWord.compHOL ctxt p labels).1 * (wordCodeSize code+1) * (6*limit+1)

/-- Word-visit bound used as the Stack clock for the actual compiled entry. -/
noncomputable def tailStackReplayLimit (ac : AsmConfigExact 64) (count name alg regCount : Nat)
    (col : Option (Spt Nat)) (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (limit : Nat) : Nat :=
  let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
  sizeOf out * (wordCodeSize code+1) * (tailWordReplayLimit p ctxt labels code limit+1)

/-- A completed supported Loop tail entry yields an actual bounded RISC-V run
through the full Word compiler and a related compiled code table. The backend
initialization and resource premises are explicit; no callee-shape premise is
needed for the compiled Word table. -/
theorem singleTail_compiledCode_riscvWithin {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
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
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64) (start argumentCount : Nat)
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
    (found : sptLookup start entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 argumentCount regCount (bs,n)).1)
    (inputCode : List (Nat × HolProg 64)) (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat) (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat)
    (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : entry.code = sptFromAList inputCode)
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
    let stackLimit := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F)
      (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := stackLimit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame))) + 4)) ∧
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
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) := by
  obtain ⟨outShape,localCode,outNoInstall,outFlat,outConvention,wordPost,wordResult,perm,selectedLocals,targetPost,
    wordRel,wordFfi,targetRel,targetRun,targetBound⟩ :=
    singleTail_compiledCode_word_bound ac count name alg regCount col shape calleeShape source sourcePost result
      word ctxt labels compiledCode locals limit lookup premises complete gc noInstall codeRel codeDomain localsRel domain sourceBound
  obtain ⟨wordComplete,_,wordNotTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have compiledNoInstall := Flapjack.Compiler.Backend.WordToWord.noInstallCode_of_codeRel word.code compiledCode codeRel codeDomain noInstall
  have notError : wordResult ≠ some .error := by cases wordComplete <;> simp
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,stackRelation⟩ :=
    allocatedRegTailRiscVWithin ac _ outShape
      {word with code := compiledCode,locals := locals,clock := tailWordReplayLimit p ctxt labels compiledCode limit}
      targetPost wordResult entry regCount frameSize frame
      (tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit) lens bs bsPost n nPost
      compiled start argumentCount outNoInstall compiledNoInstall localCode wordComplete wordNotTimeout
      (by simpa [tailWordReplayLimit,tailStackReplayLimit] using targetBound)
      ⟨by simpa [tailWordReplayLimit] using targetRun,notError,stackRel,outConvention,outFlat,native,lengthBound,bitmapBound,bitmapPrefix,labelCheck,maxBound⟩
      frameDef frameSizeDef space found inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab
      pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor labRel hpc hmc tie machineRel
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
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,
    wordPost,wordResult,perm,selectedLocals,targetPost,wordRel,wordFfi,targetRel,stackRelation,correspondence⟩

end SteppedFlapjack.LoopToWordSteps
