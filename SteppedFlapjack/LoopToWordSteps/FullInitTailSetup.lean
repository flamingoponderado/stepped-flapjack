import SteppedFlapjack.LoopToWordSteps.TailEntryRiscV
import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
import SteppedFlapjack.StackToLabSteps.EntryLocation
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import SteppedFlapjack.LoopToWordSteps.FullInitFilteredTailRiscV
import SteppedFlapjack.WordToStackSteps.TailEntryFrame

/-! Packaged full-initialization backend for supported Loop entries. -/
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

/-- Compiler and full-initialization witnesses for a Loop entry with a
fitting native frame. -/
structure FullInitTailSetup {F : Type} (p : HolLoopProg 64)
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
  found : sptLookup firstLoopName entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      (fullCompileSingle ac.twoRegArith regCount alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2 argumentCount regCount (bs,n)).1
  stackConf : StackToLab.Config
  dataConf : DataToWord.Config
  maxHeap : Nat
  sp : Nat
  offset : BitVec 64 × BitVec 64
  bitmaps : List (BitVec 64)
  inputCode : List (Nat × HolProg 64)
  lab : LabSem.State 64 LabToTarget.Config F
  saveRegs : Nat → Bool
  dataSp : Nat
  coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64)
  initAssumptions : Assumptions stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp coracle
  entryEq : entry = {(fullMakeInit stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp coracle).1 with clock := entry.clock}
  pc : BitVec 64
  mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection
  labCode : LabSem.LabProgHOL 64
  labs : Spt (Spt Nat)
  asm : AsmState 64
  machine : RiscV.L3.riscv_state
  hmc : mc.target = riscvTarget
  machineLab : LabSem.State 64 LabToTarget.Config F := lab
  labRelation : LabExecutionLink machineLab lab
  tie : LabToTarget.oracleTie mc machine machineLab
  machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) machineLab asm machine

/-- Explicit tick bound for the initialized backend. -/
noncomputable def FullInitTailSetup.tickLimit {F : Type} {p : HolLoopProg 64}
    {word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F} {limit : Nat}
    (setup : FullInitTailSetup p word limit) : Nat :=
  let out := (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
    ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2
  let stackLimit := tailStackReplayLimit setup.ac setup.count setup.name setup.alg setup.regCount
    setup.col p setup.ctxt setup.labels setup.compiledCode limit
  let base := InitMake.makeInitAny (StackToLab.isGenGc setup.dataConf.gcKind) setup.maxHeap setup.bitmaps setup.dataSp
    (coracle1 setup.coracle) setup.stackConf.jump setup.offset setup.sp (sptFromAList (code1 setup.dataConf setup.inputCode))
    (s2 setup.stackConf setup.dataConf setup.maxHeap setup.sp setup.offset setup.inputCode setup.lab setup.saveRegs setup.coracle)
  let cost := uniformFactor (width := 64) setup.dataConf *
    (3 + callSequenceCost setup.ac stackLimit setup.entry.code out (setup.bs,setup.n)
      (setup.regCount,setup.frameSize,setup.frame))
  labTickBound 4 setup.labCode setup.lab.codeBuffer * (flattenStepFactor *
    (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc setup.dataConf.gcKind) setup.maxHeap setup.sp : HolProg 64) +
      computedRunCost setup.offset cost (.call none (.inl firstLoopName) none) base * cost + 4))

/-- A compatible full-initialization setup runs a bounded Loop entry and
preserves its observable outcome or the resource-limit alternative. -/
theorem FullInitTailSetup.run_bounded {F : Type} {loc : Nat} {p callee : HolLoopProg 64}
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (setup : FullInitTailSetup p word limit)
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
  have resultBound : ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ setup.tickLimit ∧
      evaluateTargetHOL setup.mc setup.lab.ffi ticks setup.machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
    have buffer : setup.machineLab.codeBuffer = setup.lab.codeBuffer := setup.labRelation.codeBuffer
    obtain ⟨outcome,ticks,finalMachine,finalFfi,_,_,bound,run,_,_,_,_,_,_,_,_,_,_,_,correspondence,_⟩ :=
      singleTail_fullInit_filtered_riscvWithin setup.ac setup.count setup.name setup.alg setup.regCount setup.col shape calleeShape
        source sourcePost result word setup.ctxt setup.labels setup.compiledCode setup.locals limit lookup premises complete
        setup.gc setup.noInstall setup.codeRel setup.codeDomain setup.localsRel setup.domain sourceBound setup.entry
        setup.frameSize setup.frame setup.lens setup.bs setup.bsPost setup.n setup.nPost setup.compiled setup.argumentCount
        setup.stackRel setup.native setup.lengthBound setup.bitmapBound setup.bitmapPrefix setup.labelCheck setup.maxBound
        setup.frameDef setup.frameSizeDef setup.space setup.found setup.stackConf setup.dataConf setup.maxHeap setup.sp
        setup.offset setup.bitmaps setup.inputCode setup.lab setup.machineLab setup.saveRegs setup.dataSp setup.coracle setup.initAssumptions
        setup.entryEq setup.pc setup.mc setup.labCode setup.labs setup.asm setup.machine setup.hmc setup.labRelation setup.tie setup.machineRel
    refine ⟨outcome,ticks,finalMachine,finalFfi,?_,run,?_⟩
    · simpa [FullInitTailSetup.tickLimit,buffer] using bound
    · rcases correspondence with good | ⟨resource,events,_⟩
      · exact Or.inl good
      · exact Or.inr ⟨resource,events⟩
  exact resultBound


end SteppedFlapjack.LoopToWordSteps
