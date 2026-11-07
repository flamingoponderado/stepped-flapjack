import SteppedFlapjack.LoopToWordSteps.FullInitTailSetup

/-! Discharge the resource alternative using the actual compiled Word run. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps

/-- The computed optimized Word entry remains within its recorded stack limit. -/
noncomputable def FullInitTailSetup.wordSafe {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : FullInitTailSetup p word limit) : Prop :=
  let out := (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
    ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2
  let post := (WordSemStateFiniteExact.evaluate out
    {word with code := setup.compiledCode, locals := setup.locals, clock := tailWordReplayLimit p setup.ctxt setup.labels setup.compiledCode limit}).2
  post.stackMax.getD (post.stackLimit+1) ≤ post.stackLimit

/-- A bounded source run has a matching bounded RISC-V outcome when the
actual optimized Word run remains within its stack limit. -/
theorem FullInitTailSetup.run_bounded_safe {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (setup : FullInitTailSetup p word limit)
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL setup.ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k setup.ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit)
    (safe : setup.wordSafe) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents := by
  rcases setup.labRelation with same | filtered
  · have tie : LabToTarget.oracleTie setup.mc setup.machine setup.lab := by simpa only [same] using setup.tie
    have rel : LabToTarget.stateRel (setup.mc,setup.labCode,setup.labs,setup.pc) setup.lab setup.asm setup.machine := by
      simpa only [same] using setup.machineRel
    obtain ⟨outcome,ticks,finalMachine,finalFfi,_,_,bound,run,_,_,_,_,_,_,targetPost,_,_,_,_,correspondence,targetRun⟩ :=
      singleTail_fullInit_riscvWithin setup.ac setup.count setup.name setup.alg setup.regCount setup.col shape calleeShape
        source sourcePost result word setup.ctxt setup.labels setup.compiledCode setup.locals limit lookup premises complete
        setup.gc setup.noInstall setup.codeRel setup.codeDomain setup.localsRel setup.domain sourceBound setup.entry
        setup.frameSize setup.frame setup.lens setup.bs setup.bsPost setup.n setup.nPost setup.compiled setup.argumentCount
        setup.stackRel setup.native setup.lengthBound setup.bitmapBound setup.bitmapPrefix setup.labelCheck setup.maxBound
        setup.frameDef setup.frameSizeDef setup.space setup.found setup.stackConf setup.dataConf setup.maxHeap setup.sp
        setup.offset setup.bitmaps setup.inputCode setup.lab setup.saveRegs setup.dataSp setup.coracle setup.initAssumptions
        setup.entryEq setup.pc setup.mc setup.labCode setup.labs setup.asm setup.machine setup.hmc tie rel
    have postSafe : targetPost.stackMax.getD (targetPost.stackLimit+1) ≤ targetPost.stackLimit := by
      unfold FullInitTailSetup.wordSafe at safe
      dsimp only at safe
      rw [targetRun] at safe
      exact safe
    refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,?_⟩
    · simpa [FullInitTailSetup.tickLimit] using bound
    · rcases correspondence with good | ⟨_,_,bad⟩
      · exact good
      · omega
  · have buffer : setup.machineLab.codeBuffer = setup.lab.codeBuffer := filtered.codeBuffer
    obtain ⟨outcome,ticks,finalMachine,finalFfi,_,_,bound,run,_,_,_,_,_,_,targetPost,_,_,_,_,correspondence,targetRun⟩ :=
      singleTail_fullInit_filtered_riscvWithin setup.ac setup.count setup.name setup.alg setup.regCount setup.col shape calleeShape
        source sourcePost result word setup.ctxt setup.labels setup.compiledCode setup.locals limit lookup premises complete
        setup.gc setup.noInstall setup.codeRel setup.codeDomain setup.localsRel setup.domain sourceBound setup.entry
        setup.frameSize setup.frame setup.lens setup.bs setup.bsPost setup.n setup.nPost setup.compiled setup.argumentCount
        setup.stackRel setup.native setup.lengthBound setup.bitmapBound setup.bitmapPrefix setup.labelCheck setup.maxBound
        setup.frameDef setup.frameSizeDef setup.space setup.found setup.stackConf setup.dataConf setup.maxHeap setup.sp
        setup.offset setup.bitmaps setup.inputCode setup.lab setup.machineLab setup.saveRegs setup.dataSp setup.coracle setup.initAssumptions
        setup.entryEq setup.pc setup.mc setup.labCode setup.labs setup.asm setup.machine setup.hmc filtered setup.tie setup.machineRel
    have postSafe : targetPost.stackMax.getD (targetPost.stackLimit+1) ≤ targetPost.stackLimit := by
      unfold FullInitTailSetup.wordSafe at safe
      dsimp only at safe
      rw [targetRun] at safe
      exact safe
    refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,?_⟩
    · simpa [FullInitTailSetup.tickLimit,buffer] using bound
    · rcases correspondence with good | ⟨_,_,bad⟩
      · exact good
      · omega

end SteppedFlapjack.LoopToWordSteps
