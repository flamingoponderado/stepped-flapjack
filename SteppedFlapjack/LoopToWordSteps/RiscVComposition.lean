import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.LoopToWordSteps.StackReady

/-! Compose the proved Loop-to-Word fragment through the RISC-V backend. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps

/-- A complete Loop run in the shared fragment produces a bounded RISC-V
run through the actual compiled entry; the intermediate Word run and its
step bound are proved rather than supplied. The computed bound uses a finite
oracle prefix selected by the supplied limit; it is not generally linear with
constants determined only by the source program. -/
theorem stackReady_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (p : HolLoopProg 64) (shape : StackReady p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (k frameSize frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64) (start argumentCount : Nat)
    (complete : CompleteLoopResult result) (stepBound : LoopSteps.steps p source ≤ limit)
    (loopPremises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
    (wordPremises : stateRel ac k frameSize frame word {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt p labels).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt p labels).1 = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false (LoopToWord.compHOL ctxt p labels).1 (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt p labels).1 < 2*frame+2*k)
    (frameDef : frame = max (maxVarHOL (LoopToWord.compHOL ctxt p labels).1 / 2 + 1 - k) (argumentCount-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize - (argumentCount-k) ≤ entry.stackSpace)
    (found : sptLookup start entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false (LoopToWord.compHOL ctxt p labels).1 argumentCount k (bs,n)).1)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code (LoopToWord.compHOL ctxt p labels).1 (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code (LoopToWord.compHOL ctxt p labels).1 (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
        (wordResult : Option (WordSemResult 64)),
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 word = (wordResult,wordPost) ∧
        wordPost.ffi = sourcePost.ffi ∧
        LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
        compCorrectResult ac k frameSize frame {word with clock := limit}
          {wordPost with clock := limit - (word.clock - wordPost.clock)} stackPost wordResult stackResult lens ∧
        ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents ∧
            wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  have loopCorrect := directProgram_correct_with_steps (C := Nat × LabToTarget.Config)
    (stackReady_directProgram shape) source
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRelation,wordBound⟩ :=
    loopCorrect result sourcePost word ctxt (.loc 1 0) labels loopPremises
  obtain ⟨wordComplete,wordNotError,wordNotTimeout⟩ :=
    completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRelation
  have wordShape : CallSequence (LoopToWord.compHOL ctxt p labels).1 := .block (stackReady_wordBlock shape ctxt labels)
  have noInstall := stackReady_noInstall shape ctxt labels
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,stackRelation⟩ :=
    allocatedWordSequenceRiscVWithin ac _ wordShape word wordPost wordResult entry k frameSize frame limit lens bs bsPost n nPost
      compiled start argumentCount noInstall noInstallCode wordCode wordComplete wordNotTimeout (wordBound.trans stepBound)
      ⟨wordRun,wordNotError,wordPremises⟩ frameDef frameSizeDef space found inputCode anything cr c jump bounds pointer f gen
      maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  have wordOutcome := loopWordOutcome_of_resultCase ctxt word wordPost sourcePost result wordResult complete wordRelation
  have correspondence := loopMachine_correspondence ac k frameSize frame lens
    {word with clock := limit} {wordPost with clock := limit - (word.clock - wordPost.clock)}
    sourcePost stackPost result wordResult stackResult outcome finalFfi wordFfi wordOutcome
    stackRelation classification events
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,
    wordPost,wordResult,wordRun,wordFfi,wordRelation,stackRelation,correspondence⟩

end SteppedFlapjack.LoopToWordSteps
