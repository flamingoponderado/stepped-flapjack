import SteppedFlapjack.LoopToWordSteps.NativeTailCompilerFacts
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
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

/-- Remaining Stack-to-machine witnesses, after the Word compiler and native
frame have been initialized. -/
structure NativeTailMachineSetup {F : Type}
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) (name stackReplay : Nat) where
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
  sourceCode : stack.code = sptFromAList inputCode
  pre : Pre cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} stack.regs
  relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} 0 stack.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed)
  ha : ¬renamed.useAlloc
  hs : ¬renamed.useStore
  hk : ¬renamed.useStack
  hf : Function.Bijective (findNameSpt f)
  hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput))
  hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle
  labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab
  hpc : LabSem.locToPc name 0 lab.code = some lab.pc
  hmc : mc.target = riscvTarget
  tie : LabToTarget.oracleTie mc machine lab
  machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine

/-- RISC-V tick limit for failure to allocate the native entry frame. -/
noncomputable def NativeTailMachineSetup.resourceTickLimit {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} {name stackReplay : Nat}
    (backend : NativeTailMachineSetup stack name stackReplay) : Nat :=
  labTickBound 4 backend.labCode backend.lab.codeBuffer *
    (flattenStepFactor * (computedRunCost backend.bounds (uniformFactor (width := 64) backend.c * 3)
      (.call none (.inl name) none)
      (Tgt backend.anything backend.cr backend.c
        {stack with code := sptFromAList (StackRawCall.compile backend.inputCode),clock := stackReplay+1} 0 stack.regs) *
      (uniformFactor (width := 64) backend.c * 3) + 4))

/-- Machine tick limit computed from the whole compiler's selected bitmap
and frame, independently of the setup witness. -/
noncomputable def NativeTailMachineSetup.successTickLimit {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} {name stackReplay : Nat}
    (backend : NativeTailMachineSetup stack name stackReplay)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) : Nat :=
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let out := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((name,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs name)).2.2
  let bitmap := (nativeEntryBitmap ac false k name (compile wc ac programs).2 (.list [4],1)).getD (.list [],0)
  let frame := max (maxVarHOL out / 2 + 1-k) (1-k)
  let frameSize := if frame = 0 then 0 else frame+1
  let cost := uniformFactor (width := 64) backend.c *
    (3 + callSequenceCost ac stackReplay stack.code out bitmap (k,frameSize,frame))
  labTickBound 4 backend.labCode backend.lab.codeBuffer *
    (flattenStepFactor * (computedRunCost backend.bounds cost (.call none (.inl name) none)
      (Tgt backend.anything backend.cr backend.c
        {stack with code := sptFromAList (StackRawCall.compile backend.inputCode),clock := stackReplay+1} 0 stack.regs) * cost + 4))

/-- The actual whole compiler constructs a `TailRiscVSetup` from a valid native
Stack initialization and the remaining Stack-to-machine witnesses, or yields
an actual bounded RISC-V resource-limit outcome for a failed entry frame. -/
theorem nativeTail_setup_or_resource {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (name : Nat)
    (shapes : TailProgramShapes programs)
    (member : (name,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit : Nat)
    (backend : NativeTailMachineSetup stack name (tailStackReplayLimit ac 1 name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) (entryColour wc programs name) p ctxt labels
      (sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2) limit)) :
    (∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
       (setup : TailRiscVSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      setup.tickLimit = backend.successTickLimit wc ac programs p ctxt labels ∧
      ∃ frameSize,
        word = {Flapjack.WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
            stack (sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2) coracle)
          with code := sptFromAList programs}) ∨
    ∃ ticks finalMachine finalFfi,
      ticks ≤ backend.resourceTickLimit ∧
      evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine =
        (.halt .resourceLimitHit,finalMachine,finalFfi) ∧ finalFfi.ioEvents = stack.ffi.ioEvents := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2
  let originalCode := sptFromAList programs
  let replay := tailWordReplayLimit p ctxt labels compiledCode limit
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,native,found,lengthBound,bitmapBound,bitmapPrefix,frameResult⟩ :=
    nativeTail_compilerFacts_or_resource wc ac programs p ctxt labels name shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit
  rcases frameResult with facts | resource
  · obtain ⟨noInstall,codeRel,codeDomain,domain,localsRel,lookup,labelCheck,maxBound,space,stackRel⟩ := facts
    let base := Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle
    let word := {Flapjack.WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base with code := originalCode}
    let entry := {stack with clock := replay}
    have stackGc : gcFunConstOk stack.gcFun := by
      have gcEq : stack.gcFun = Flapjack.Compiler.Backend.WordGcFunctions.wordGcFun backend.c := backend.pre.gcFun
      rw [gcEq]
      exact Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcFunConstOkWordGcFun
    have gc : gcFunConstOk word.gcFun := by
      simpa [word,base,Flapjack.WordSemStateFiniteExact.callEnv,
        Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit] using stackGc
    let setup : TailRiscVSetup p word limit := {
      ac := ac, count := 1, name := name, alg := wc.regAlg, regCount := k,
      col := entryColour wc programs name, ctxt := ctxt, labels := labels, compiledCode := compiledCode,
      locals := word.locals, gc := gc, noInstall := noInstall, codeRel := codeRel, codeDomain := codeDomain,
      localsRel := localsRel, domain := domain, entry := entry, frameSize := frameSize, frame := frame, lens := [],
      bs := bs, bsPost := bsPost, n := n, nPost := nPost, compiled := body, start := name, argumentCount := 1,
      stackRel := by simpa [entry] using stackRel,
      native := native, lengthBound := lengthBound, bitmapBound := by simpa [entry] using bitmapBound,
      bitmapPrefix := by simpa [entry] using bitmapPrefix,
      labelCheck := by simpa [entry] using labelCheck, maxBound := maxBound, frameDef := frameDef,
      frameSizeDef := sizeDef, space := by simpa [entry] using space, found := by simpa [entry] using found,
      inputCode := backend.inputCode, anything := backend.anything, cr := backend.cr, c := backend.c,
      jump := backend.jump, bounds := backend.bounds, pointer := backend.pointer, f := backend.f, gen := backend.gen,
      maxHeap := backend.maxHeap, a := backend.a, b := backend.b, removeInput := backend.removeInput,
      oracle := backend.oracle, renamed := backend.renamed, lab := backend.lab, pc := backend.pc, mc := backend.mc,
      labCode := backend.labCode, labs := backend.labs, asm := backend.asm, machine := backend.machine,
      distinct := backend.distinct, sourceCode := by simpa [entry] using backend.sourceCode,
      pre := by simpa [entry,k,compiledCode] using backend.pre,
      relation := by simpa [entry,k,compiledCode] using backend.relation,
      ha := backend.ha, hs := backend.hs, hk := backend.hk, hf := backend.hf, hcode := backend.hcode,
      hor := backend.hor, labRel := backend.labRel, hpc := backend.hpc, hmc := backend.hmc,
      tie := backend.tie, machineRel := backend.machineRel }
    have tickEq : setup.tickLimit = backend.successTickLimit wc ac programs p ctxt labels := by
      dsimp only [setup,TailRiscVSetup.tickLimit,NativeTailMachineSetup.successTickLimit,entry,k,compiledCode]
      rw [selected]
      simp only [Option.getD_some,← frameDef,← sizeDef]
    exact Or.inl ⟨word,setup,rfl,rfl,rfl,rfl,tickEq,frameSize,rfl⟩
  · obtain ⟨post,run,ffi,bound⟩ := resource
    obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
      stackPipelineRiscVWithin backend.inputCode stack name _ 3 (some (.halt (.word 2))) post
        backend.anything backend.cr backend.c backend.jump backend.bounds backend.pointer backend.f
        backend.gen backend.maxHeap backend.a backend.b backend.removeInput backend.oracle backend.renamed backend.lab
        HolOutcome.resourceLimitHit backend.pc backend.mc backend.labCode backend.labs backend.asm backend.machine
        backend.distinct backend.sourceCode run (by simp) bound backend.pre backend.relation backend.ha backend.hs backend.hk
        backend.hf backend.hcode backend.hor backend.labRel backend.hpc (by simp [stackEntryClass]) backend.hmc backend.tie backend.machineRel
    exact Or.inr ⟨ticks,finalMachine,finalFfi,by simpa [NativeTailMachineSetup.resourceTickLimit] using tickBound,
      machineRun,by simpa only [ffi] using events⟩

end SteppedFlapjack.LoopToWordSteps
