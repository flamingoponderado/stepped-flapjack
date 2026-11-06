import SteppedFlapjack.WordToStackSteps.WholeEntryFrame

/-! Actual initial entry allocation and the RISC-V resource path. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs.InitializationStateRel Flapjack.WordSemStateFiniteExact

/-- The actual initial entry either has a related allocated Word/Stack state,
or executes to the RISC-V resource limit with its corresponding tick bound. -/
theorem wholeWordStack_entryFrame_or_riscvResource {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name : Nat) (p : WordLangProgHOL (BitVec 64)) (member : (name,1,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (shape : LoopSequence p)
    (t : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle)
    (limit : Nat)
    (inputCode : List (Nat × HolProg 64))
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : t.code = sptFromAList inputCode)
    (pre : Pre cr c {t with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} t.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {t with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 t.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc name 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ col q bs n bsPost nPost body frame frameSize,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,1,p),col)).2.2 ∧
      LoopBlock q ∧ noInstallSubprogsHOL q = true ∧ flatExpConventions q = true ∧
      postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) q = true ∧
      frame = max (maxVarHOL q / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name t.code = some (compileProgNative ac false q 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ t.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (t.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) t (sptFromAList (compile wc ac programs).2) coracle))
        {t with stackSpace := t.stackSpace-frameSize} [] 0 ∧
       stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        {(callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) t (sptFromAList (compile wc ac programs).2) coracle)) with clock := limit}
        {t with stackSpace := t.stackSpace-frameSize,clock := limit} [] 0 ∨
       ∃ (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
         ticks ≤ labTickBound 4 labCode lab.codeBuffer *
          (flattenStepFactor * (computedRunCost bounds (uniformFactor (width := 64) c * 3)
            (.call none (.inl name) none)
            (Tgt anything cr c {t with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 t.regs) *
            (uniformFactor (width := 64) c * 3) + 4)) ∧
         evaluateTargetHOL mc lab.ffi ticks machine = (.halt HolOutcome.resourceLimitHit,finalMachine,finalFfi) ∧
         finalFfi.ioEvents = t.ffi.ioEvents) := by
  obtain ⟨col,q,bs,n,bsPost,nPost,body,frame,frameSize,qDef,block,noInstall,flat,postAlloc,
    frameDef,sizeDef,compilation,found,lengthBound,gapBound,bitmapPrefix,caseResult⟩ :=
    wholeWordStack_entryFrame_or_resource wc ac programs name p member nodup shape t coracle noRaise noStore codeEq bitmapsPrefix ok limit
  refine ⟨col,q,bs,n,bsPost,nPost,body,frame,frameSize,qDef,block,noInstall,flat,postAlloc,
    frameDef,sizeDef,compilation,found,lengthBound,gapBound,bitmapPrefix,?_⟩
  rcases caseResult with success | ⟨post,run,ffi,stepBound⟩
  · exact Or.inl success
  · right
    have classification : stackEntryClass (some (.halt (.word 2)) : Option (StackSemResult 64)) =
        .CompleteResult HolOutcome.resourceLimitHit := by simp [stackEntryClass]
    obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
      stackPipelineRiscVWithin inputCode t name (limit+1) 3 (some (.halt (.word 2))) post
        anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab HolOutcome.resourceLimitHit
        pc mc labCode labs asm machine distinct sourceCode run (by simp) stepBound pre relation ha hs hk hf hcode hor rel hpc classification hmc tie machineRel
    exact ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,by simpa only [ffi] using events⟩

end SteppedFlapjack.WordToStackSteps
