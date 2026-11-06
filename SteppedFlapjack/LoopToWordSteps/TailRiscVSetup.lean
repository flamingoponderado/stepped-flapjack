import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.DirectTailRiscV
import SteppedFlapjack.WordAllocSteps.WholeTailCode

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

/-- Concrete compiler, state and resource witnesses for running a Loop entry
through the RISC-V backend. Grouping these witnesses lets source-specific
proofs share the backend interface. -/
structure TailRiscVSetup {F : Type} (p : HolLoopProg 64)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat) where
  ac : AsmConfigExact 64
  count : Nat
  name : Nat
  alg : Nat
  regCount : Nat
  col : Option (Spt Nat)
  ctxt : Spt Nat
  labels : Nat × Nat
  compiledCode : Spt (Nat × WordLangProgHOL (BitVec 64))
  locals : Spt (WordLocW 64)
  gc : gcFunConstOk word.gcFun
  noInstall : WordProps.noInstallCode word.code
  codeRel : codeRel word.code compiledCode
  codeDomain : sptDomain word.code = sptDomain compiledCode
  localsRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals
  domain : sptDomain locals = (fun key => key ∈ evenList count)
  entry : StackSemStateFiniteExact 64 LabToTarget.Config F
  frameSize : Nat
  frame : Nat
  lens : List Nat
  bs : AppList (BitVec 64)
  bsPost : AppList (BitVec 64)
  n : Nat
  nPost : Nat
  compiled : HolProg 64
  start : Nat
  argumentCount : Nat
  stackRel : stateRel ac regCount frameSize frame
      {word with code := compiledCode,locals := locals,clock := tailWordReplayLimit p ctxt labels compiledCode limit}
      {entry with stackSpace := entry.stackSpace-(frameSize-(argumentCount-regCount))} lens 0
  native : Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2
      (bs,n) (regCount,frameSize,frame) = (compiled,(bsPost,nPost))
  lengthBound : (appListAppend bs).length ≤ n
  bitmapBound : n-(appListAppend bs).length ≤ entry.bitmaps.length
  bitmapPrefix : List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length))
  labelCheck : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc
  maxBound : maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 < 2*frame+2*regCount
  frameDef : frame = max (maxVarHOL (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 / 2 + 1 - regCount) (argumentCount-regCount)
  frameSizeDef : frameSize = if frame = 0 then 0 else frame+1
  space : frameSize-(argumentCount-regCount) ≤ entry.stackSpace
  found : sptLookup start entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 argumentCount regCount (bs,n)).1
  inputCode : List (Nat × HolProg 64)
  anything : WordSemGcFun 64
  cr : CompileFn 64 LabToTarget.Config
  c : DataToWord.Config
  jump : Bool
  bounds : BitVec 64 × BitVec 64
  pointer : Nat
  f : Spt Nat
  gen : Bool
  maxHeap : Nat
  a : Nat
  b : Nat
  removeInput : List (Nat × HolProg 64)
  oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64)
  renamed : StackSemStateFiniteExact 64 LabToTarget.Config F
  lab : LabSem.State 64 LabToTarget.Config F
  pc : BitVec 64
  mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection
  labCode : LabSem.LabProgHOL 64
  labs : Spt (Spt Nat)
  asm : AsmState 64
  machine : RiscV.L3.riscv_state
  distinct : (inputCode.map Prod.fst).Nodup
  sourceCode : entry.code = sptFromAList inputCode
  pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit+1} entry.regs
  relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := tailStackReplayLimit ac count name alg regCount col p ctxt labels compiledCode limit+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed)
  ha : ¬renamed.useAlloc
  hs : ¬renamed.useStore
  hk : ¬renamed.useStack
  hf : Function.Bijective (findNameSpt f)
  hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput))
  hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle
  labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab
  hpc : LabSem.locToPc start 0 lab.code = some lab.pc
  hmc : mc.target = riscvTarget
  tie : LabToTarget.oracleTie mc machine lab
  machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine

/-- Run a completed Loop entry using a packaged backend setup. -/
theorem TailRiscVSetup.run {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (setup : TailRiscVSetup p word limit)
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL setup.ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k setup.ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    let out := (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2
    let stackLimit := tailStackReplayLimit setup.ac setup.count setup.name setup.alg setup.regCount setup.col p setup.ctxt setup.labels setup.compiledCode limit
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F)
      (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 setup.labCode setup.lab.codeBuffer *
        (flattenStepFactor * (computedRunCost setup.bounds
          (uniformFactor (width := 64) setup.c * (3 + callSequenceCost setup.ac stackLimit setup.entry.code out (setup.bs,setup.n) (setup.regCount,setup.frameSize,setup.frame)))
          (.call none (.inl setup.start) none)
          (Tgt setup.anything setup.cr setup.c {setup.entry with code := sptFromAList (StackRawCall.compile setup.inputCode),clock := stackLimit+1} 0 setup.entry.regs) *
          (uniformFactor (width := 64) setup.c * (3 + callSequenceCost setup.ac stackLimit setup.entry.code out (setup.bs,setup.n) (setup.regCount,setup.frameSize,setup.frame))) + 4)) ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧ stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ wordPost wordResult perm selectedLocals targetPost,
        LoopToWord.CompileCorrect.resultCase setup.ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
        wordPost.ffi = sourcePost.ffi ∧
        wordStateEqRel {wordPost with code := setup.compiledCode,permute := perm,locals := selectedLocals,clock := tailWordReplayLimit p setup.ctxt setup.labels setup.compiledCode limit-(6*limit-(6*limit-(word.clock-wordPost.clock)))} targetPost ∧
        compCorrectResult setup.ac setup.regCount setup.frameSize setup.frame
          {word with code := setup.compiledCode,locals := setup.locals,clock := stackLimit}
          {targetPost with clock := stackLimit-(tailWordReplayLimit p setup.ctxt setup.labels setup.compiledCode limit-targetPost.clock)}
          stackPost wordResult stackResult setup.lens ∧
        ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents ∧
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) := by
  exact singleTail_compiledCode_riscvWithin setup.ac setup.count setup.name setup.alg setup.regCount setup.col shape calleeShape source sourcePost result word setup.ctxt setup.labels setup.compiledCode setup.locals limit lookup premises complete setup.gc setup.noInstall setup.codeRel setup.codeDomain setup.localsRel setup.domain sourceBound setup.entry setup.frameSize setup.frame setup.lens setup.bs setup.bsPost setup.n setup.nPost setup.compiled setup.start setup.argumentCount setup.stackRel setup.native setup.lengthBound setup.bitmapBound setup.bitmapPrefix setup.labelCheck setup.maxBound setup.frameDef setup.frameSizeDef setup.space setup.found setup.inputCode setup.anything setup.cr setup.c setup.jump setup.bounds setup.pointer setup.f setup.gen setup.maxHeap setup.a setup.b setup.removeInput setup.oracle setup.renamed setup.lab setup.pc setup.mc setup.labCode setup.labs setup.asm setup.machine setup.distinct setup.sourceCode setup.pre setup.relation setup.ha setup.hs setup.hk setup.hf setup.hcode setup.hor setup.labRel setup.hpc setup.hmc setup.tie setup.machineRel

/-- The machine-tick budget induced by the packaged compiler and initial state. -/
noncomputable def TailRiscVSetup.tickLimit {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : TailRiscVSetup p word limit) : Nat :=
  let out := (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
    ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2
  let stackLimit := tailStackReplayLimit setup.ac setup.count setup.name setup.alg setup.regCount
    setup.col p setup.ctxt setup.labels setup.compiledCode limit
  let cost := uniformFactor (width := 64) setup.c *
    (3 + callSequenceCost setup.ac stackLimit setup.entry.code out (setup.bs,setup.n)
      (setup.regCount,setup.frameSize,setup.frame))
  labTickBound 4 setup.labCode setup.lab.codeBuffer *
    (flattenStepFactor * (computedRunCost setup.bounds cost (.call none (.inl setup.start) none)
      (Tgt setup.anything setup.cr setup.c
        {setup.entry with code := sptFromAList (StackRawCall.compile setup.inputCode),clock := stackLimit+1}
        0 setup.entry.regs) * cost + 4))

/-- A packaged backend setup yields a bounded machine run with observable outcome correspondence. -/
theorem TailRiscVSetup.run_bounded {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (setup : TailRiscVSetup p word limit)
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (lookup : sptLookup loc source.code = some ([],callee))
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL setup.ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k setup.ctxt))
    (complete : CompleteLoopResult result) (sourceBound : LoopSteps.steps p source ≤ limit) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  obtain ⟨outcome,ticks,finalMachine,finalFfi,_,_,bound,run,_,_,_,_,_,_,_,_,_,_,_,correspondence⟩ :=
    setup.run source sourcePost result word limit shape calleeShape lookup premises complete sourceBound
  refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,?_⟩
  · simpa [TailRiscVSetup.tickLimit] using bound
  · rcases correspondence with good | ⟨resource,events,_⟩
    · exact Or.inl good
    · exact Or.inr ⟨resource,events⟩

/-- Every compatible backend setup produces a bounded machine execution. -/
def TailRiscVReady {F : Type} (p : HolLoopProg 64)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat) : Prop :=
  ∀ (setup : TailRiscVSetup p word limit),
    LoopToWord.localsRelHOL setup.ctxt source.locals word.locals →
    sptLookup 0 word.locals = some (.loc 1 0) → goodDimindex 64 →
    ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true →
    (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k setup.ctxt) →
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents))

/-- Turn the Loop-side simulation facts into the packaged backend interface. -/
theorem tailRiscVReady_of_loop {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (shape : SingleTailEntryShape loc p) (calleeShape : LoopSequenceSource callee)
    (lookup : sptLookup loc source.code = some ([],callee))
    (run : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost))
    (notError : result ≠ some .error) (rel : loopToWordStateRelHOLExact source word)
    (complete : CompleteLoopResult result) (bound : LoopSteps.steps p source ≤ limit) :
    TailRiscVReady p source sourcePost result word limit := by
  intro setup locals zero dim locWord used
  exact setup.run_bounded source sourcePost result word limit shape calleeShape lookup
    ⟨run,notError,rel,locals,zero,dim,locWord,used⟩ complete bound

end SteppedFlapjack.LoopToWordSteps
