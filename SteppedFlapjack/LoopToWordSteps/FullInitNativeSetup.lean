import SteppedFlapjack.LoopToWordSteps.FullInitTailSetup
import SteppedFlapjack.LoopToWordSteps.NativeTailCompilerFacts
import SteppedFlapjack.StackToLabSteps.FullInitStackLabSteps
import SteppedFlapjack.LabToTargetSteps.LabRiscVComposition
import SteppedFlapjack.StackToLabSteps.EntryLocation
import SteppedFlapjack.WordToStackSteps.EntryComposition
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitFfi
import Flapjack.Compiler.Backend.StackProps.EvaluateConsts

/-! Construct a full-initialization backend from the actual native compiler. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect Flapjack.WordAlloc
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord Flapjack.WordToStackProofs.InitializationStateRel
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps

/-- Actual full initialization and machine relation for a Stack entry. -/
structure FullInitStackContext {F : Type} (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) where
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
  stackEq : stack = (fullMakeInit stackConf dataConf maxHeap sp offset bitmaps inputCode lab saveRegs dataSp coracle).1
/-- Stack initialization plus the later machine-execution relations. -/
structure FullInitMachineContext {F : Type} (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    extends FullInitStackContext stack where
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

/-- Reset the Lab clock while retaining the same machine state and all
initialization relations. This permits a clock-zero machine initializer to
serve as the entry for a source run with an arbitrary clock. -/
noncomputable def FullInitMachineContext.withClock {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F}
    (backend : FullInitMachineContext stack) (clock : Nat) :
    FullInitMachineContext
      (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.bitmaps
        backend.inputCode {backend.lab with clock := clock} backend.saveRegs backend.dataSp backend.coracle).1 where
  stackConf := backend.stackConf
  dataConf := backend.dataConf
  maxHeap := backend.maxHeap
  sp := backend.sp
  offset := backend.offset
  bitmaps := backend.bitmaps
  inputCode := backend.inputCode
  lab := {backend.lab with clock := clock}
  saveRegs := backend.saveRegs
  dataSp := backend.dataSp
  coracle := backend.coracle
  initAssumptions := by simpa [Assumptions,StackToLab.Proofs.MakeInit.memoryAssumption] using backend.initAssumptions
  stackEq := rfl
  pc := backend.pc
  mc := backend.mc
  labCode := backend.labCode
  labs := backend.labs
  asm := backend.asm
  machine := backend.machine
  hmc := backend.hmc
  machineLab := {backend.machineLab with clock := clock}
  labRelation := backend.labRelation.withClock clock
  tie := by simpa [LabToTarget.oracleTie] using backend.tie
  machineRel := LabToTarget.stateRelClock _ backend.machineLab backend.asm backend.machine clock backend.machineRel

/-- Clock adjustment retains the original machine, compiler inputs and Lab
data, while setting exactly the requested evaluation clock. -/
theorem FullInitMachineContext.withClock_fields {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F}
    (backend : FullInitMachineContext stack) (clock : Nat) :
    (backend.withClock clock).lab.clock = clock ∧
    (backend.withClock clock).lab.regs = backend.lab.regs ∧
    (backend.withClock clock).lab.memory = backend.lab.memory ∧
    (backend.withClock clock).lab.ffi = backend.lab.ffi ∧
    (backend.withClock clock).bitmaps = backend.bitmaps ∧
    (backend.withClock clock).inputCode = backend.inputCode ∧
    (backend.withClock clock).coracle = backend.coracle ∧
    (backend.withClock clock).mc = backend.mc ∧
    (backend.withClock clock).machine = backend.machine := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Full initialization preserves the Lab state's FFI state. -/
theorem FullInitStackContext.ffi_eq {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    stack.ffi = backend.lab.ffi := by
  calc
    stack.ffi = (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode backend.lab backend.saveRegs backend.dataSp backend.coracle).1.ffi :=
        congrArg (fun s => s.ffi) backend.stackEq
    _ = backend.lab.ffi := by
      rw [fullMakeInit_eq]
      simp only [StackAlloc.makeInit]
      rw [StackRemove.Proofs.InitFfi.makeInitAnyFfi]
      rfl

/-- The StackRemove initializer preserves the ambient clock, byte order and
shared-memory domain, including when initialization falls back. -/
theorem initAny_ambient {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (HolProg width)) (s : StackSemStateFiniteExact width C F) :
    let t := InitMake.makeInitAny generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s
    t.clock = s.clock ∧ t.be = s.be ∧ t.shMdomain = s.shMdomain := by
  dsimp only
  unfold InitMake.makeInitAny
  cases opt : InitMake.makeInitOpt generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer code s with
  | none => simp
  | some t =>
    simp only
    unfold InitMake.makeInitOpt at opt
    cases run : StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer, s) with
    | mk result post =>
      cases result with
      | some r => simp [run] at opt
      | none =>
        simp only [run] at opt
        split at opt
        · cases opt
          have constants := StackProps.evaluateConsts _ s none post run
          have same := InitClock.evaluateInitCodeClock generateGc maxHeap pointer s post none s.clock run
          have selfUpdate : ({s with clock := s.clock} : StackSemStateFiniteExact width C F) = s := rfl
          rw [selfUpdate, run] at same
          have clock := congrArg (fun x => x.2.clock) same
          exact ⟨by simpa [InitReduce.initReduce] using clock, by simpa [InitReduce.initReduce] using constants.2.2.2.1,
            by simpa [InitReduce.initReduce] using constants.2.2.2.2.2.2.1⟩
        · simp at opt

/-- Full initialization preserves the Lab clock, byte order and shared domain. -/
theorem FullInitStackContext.ambient_eq {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitStackContext stack) :
    stack.clock = backend.lab.clock ∧ stack.be = backend.lab.be ∧ stack.shMdomain = backend.lab.sharedMemDomain := by
  have h := initAny_ambient (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.bitmaps backend.dataSp
    (coracle1 backend.coracle) backend.stackConf.jump backend.offset backend.sp (sptFromAList (code1 backend.dataConf backend.inputCode))
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode backend.lab backend.saveRegs backend.coracle)
  have eq := backend.stackEq
  rw [fullMakeInit_eq] at eq
  constructor
  · exact (congrArg (fun s => s.clock) eq).trans (by simpa [StackAlloc.makeInit, s2, s3, StackNames.makeInit, StackToLab.Proofs.MakeInit.makeInit] using h.1)
  constructor
  · exact (congrArg (fun s => s.be) eq).trans (by simpa [StackAlloc.makeInit, s2, s3, StackNames.makeInit, StackToLab.Proofs.MakeInit.makeInit] using h.2.1)
  · exact (congrArg (fun s => s.shMdomain) eq).trans (by simpa [StackAlloc.makeInit, s2, s3, StackNames.makeInit, StackToLab.Proofs.MakeInit.makeInit] using h.2.2)

/-- A compiler-determined tick bound for a fitting native entry frame. -/
noncomputable def FullInitMachineContext.successTickLimit {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat) : Nat :=
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let out := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName)).2.2
  let bitmap := (nativeEntryBitmap ac false k firstLoopName (compile wc ac programs).2 (.list [4],1)).getD (.list [],0)
  let frame := max (maxVarHOL out / 2 + 1-k) (1-k)
  let frameSize := if frame = 0 then 0 else frame+1
  let stackLimit := tailStackReplayLimit ac 1 firstLoopName wc.regAlg k (entryColour wc programs firstLoopName)
    p ctxt labels compiledCode limit
  let base := InitMake.makeInitAny (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.bitmaps backend.dataSp
    (coracle1 backend.coracle) backend.stackConf.jump backend.offset backend.sp (sptFromAList (code1 backend.dataConf backend.inputCode))
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode backend.lab backend.saveRegs backend.coracle)
  let cost := uniformFactor (width := 64) backend.dataConf *
    (3 + callSequenceCost ac stackLimit stack.code out bitmap (k,frameSize,frame))
  labTickBound 4 backend.labCode backend.lab.codeBuffer * (flattenStepFactor *
    (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.sp : HolProg 64) +
      computedRunCost backend.offset cost (.call none (.inl firstLoopName) none) base * cost + 4))

/-- A fitting compiler-selected frame gives a full-initialization setup. -/
theorem fullInitNativeTail_setup {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (shapes : TailProgramShapes programs)
    (member : (firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : stack.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix stack.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit : Nat)
    (backend : FullInitMachineContext stack)
    (fits : nativeEntryFrameSize (ac.regCount-(5+ac.avoidRegs.length))
      (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
        ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName)).2.2 ≤ stack.stackSpace) :
    ∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
       (setup : FullInitTailSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      setup.tickLimit = backend.successTickLimit wc ac programs p ctxt labels limit ∧
      ∃ frameSize,
        word = {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
            (sptFromAList (compile wc ac programs).2) coracle) with code := sptFromAList programs} := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let originalCode := sptFromAList programs
  let replay := tailWordReplayLimit p ctxt labels compiledCode limit
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,native,found,lengthBound,bitmapBound,bitmapPrefix,facts⟩ :=
    nativeTail_compilerFacts wc ac programs p ctxt labels firstLoopName shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit fits
  obtain ⟨noInstall,codeRel,codeDomain,domain,localsRel,lookup,labelCheck,maxBound,space,stackRel⟩ := facts
  let base := makeInit ac k stack compiledCode coracle
  let word := {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base with code := originalCode}
  let entry := {stack with clock := replay}
  have stackGc : gcFunConstOk stack.gcFun := by
    rw [backend.stackEq,fullMakeInit_eq]
    simpa [StackAlloc.makeInit] using Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcFunConstOkWordGcFun (width := 64) (c := backend.dataConf)
  have gc : gcFunConstOk word.gcFun := by
    simpa [word,base,WordSemStateFiniteExact.callEnv,makeInit] using stackGc
  let setup : FullInitTailSetup p word limit := {
    ac := ac, count := 1, name := firstLoopName, alg := wc.regAlg, regCount := k,
    col := entryColour wc programs firstLoopName, ctxt := ctxt, labels := labels, compiledCode := compiledCode,
    locals := word.locals, gc := gc, noInstall := noInstall, codeRel := codeRel, codeDomain := codeDomain,
    localsRel := localsRel, domain := domain, entry := entry, frameSize := frameSize, frame := frame, lens := [],
    bs := bs, bsPost := bsPost, n := n, nPost := nPost, compiled := body, argumentCount := 1,
    stackRel := by simpa [entry] using stackRel,
    native := native, lengthBound := lengthBound, bitmapBound := by simpa [entry] using bitmapBound,
    bitmapPrefix := by simpa [entry] using bitmapPrefix,
    labelCheck := by simpa [entry] using labelCheck, maxBound := maxBound, frameDef := frameDef,
    frameSizeDef := sizeDef, space := by simpa [entry] using space, found := by simpa [entry] using found,
    stackConf := backend.stackConf, dataConf := backend.dataConf, maxHeap := backend.maxHeap, sp := backend.sp,
    offset := backend.offset, bitmaps := backend.bitmaps, inputCode := backend.inputCode, lab := backend.lab,
    saveRegs := backend.saveRegs, dataSp := backend.dataSp, coracle := backend.coracle,
    initAssumptions := backend.initAssumptions, entryEq := by simp [entry,backend.stackEq],
    pc := backend.pc, mc := backend.mc, labCode := backend.labCode, labs := backend.labs,
    asm := backend.asm, machine := backend.machine, hmc := backend.hmc, machineLab := backend.machineLab,
    labRelation := backend.labRelation, tie := backend.tie, machineRel := backend.machineRel }
  have tickEq : setup.tickLimit = backend.successTickLimit wc ac programs p ctxt labels limit := by
    dsimp only [setup,FullInitTailSetup.tickLimit,FullInitMachineContext.successTickLimit,entry,k,compiledCode]
    rw [selected]
    simp only [Option.getD_some,← frameDef,← sizeDef]
  exact ⟨word,setup,rfl,rfl,rfl,rfl,tickEq,frameSize,rfl⟩

end SteppedFlapjack.LoopToWordSteps
