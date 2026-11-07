import SteppedFlapjack.LoopToWordSteps.FullInitTailSetup
import SteppedFlapjack.LoopToWordSteps.NativeTailZeroFrame
import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import SteppedFlapjack.StackToLabSteps.FullInitRiscVSteps
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

/-- A zero-frame native entry admits the fitting initialization setup. -/
theorem fullInitNativeTail_zeroFrame_setup {F : Type}
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
    (backend : FullInitMachineContext stack) (entryBody : HolProg 64)
    (zeroEntry : sptLookup firstLoopName stack.code = some (.seq (.stackAlloc 0) entryBody))
    (enabled : stack.useStack = true)
    (enoughRegs : 1 ≤ ac.regCount-(5+ac.avoidRegs.length)) :
    (∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
       (setup : FullInitTailSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      setup.tickLimit = backend.successTickLimit wc ac programs p ctxt labels limit ∧
      ∃ frameSize,
        word = {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
            (sptFromAList (compile wc ac programs).2) coracle) with code := sptFromAList programs} ∧
        setup.ac = ac ∧ setup.count = 1 ∧ setup.name = firstLoopName ∧
        setup.alg = wc.regAlg ∧ setup.regCount = ac.regCount-(5+ac.avoidRegs.length) ∧
        setup.col = entryColour wc programs firstLoopName ∧ setup.labels = labels ∧
        setup.compiledCode = sptFromAList (compile wc ac programs).2 ∧
        setup.locals = word.locals ∧ setup.frameSize = frameSize ∧ frameSize = 0 ∧
        sptLookup firstLoopName setup.compiledCode = some (1,
          (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
            ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2)) := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let originalCode := sptFromAList programs
  let replay := tailWordReplayLimit p ctxt labels compiledCode limit
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,native,found,lengthBound,bitmapBound,bitmapPrefix,frameResult⟩ :=
    nativeTail_compilerFacts_zeroFrame wc ac programs p ctxt labels firstLoopName shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit entryBody zeroEntry enabled
  obtain ⟨noInstall,codeRel,codeDomain,domain,localsRel,lookup,labelCheck,maxBound,space,stackRel⟩ := frameResult
  have frameZero : frameSize = 0 := by
    have entryEq := found.symm.trans zeroEntry
    simp only [Option.some.injEq,compileProgNative, ← frameDef, ← sizeDef, native] at entryEq
    injection entryEq with allocation bodyEq
    injection allocation with allocationEq
    omega
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
  have outputMember := wholeCompile_contains_entryColour wc ac programs firstLoopName 1
    (LoopToWord.compHOL ctxt p labels).1 member nodup
  have outputEq : fullCompileSingle ac.twoRegArith k wc.regAlg ac
      ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName) =
      (firstLoopName,1,(fullCompileSingle ac.twoRegArith k wc.regAlg ac
        ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName)).2.2) := by
    simp [fullCompileSingle,compileSingle,k]
  rw [outputEq] at outputMember
  have outputNodup : ((compile wc ac programs).2.map Prod.fst).Nodup := by
    rw [wholeCompile_names wc ac programs]
    exact nodup
  have outputLookup : sptLookup firstLoopName compiledCode = some (1,
      (fullCompileSingle ac.twoRegArith k wc.regAlg ac
        ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName)).2.2) := by
    rw [show compiledCode = sptFromAList (compile wc ac programs).2 from rfl,sptLookup_sptFromAList]
    exact sptAListLookup_of_mem_nodup _ _ _ outputNodup outputMember
  exact ⟨word,setup,rfl,rfl,rfl,rfl,tickEq,frameSize,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frameZero,outputLookup⟩

end SteppedFlapjack.LoopToWordSteps
