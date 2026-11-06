import SteppedFlapjack.LoopToWordSteps.WordAllocatedSequence
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.EntryComposition

/-! Loop-to-Word compilation, instruction selection, and RISC-V execution. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.Compiler.Backend.WordInst Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps SteppedFlapjack.WordInstSteps
open SteppedFlapjack.WordSimpSteps Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc

/-- A completed Loop run in the selected fragment induces a bounded RISC-V
run with matching outcome and trace or a resource-limit trace prefix. -/
theorem loopSequence_wordAllocated_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (count name alg k : Nat) (col : Option (Spt Nat)) (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (locals : Spt (WordLocW 64))
    (q : WordLangProgHOL (BitVec 64))
    (selected : q = (fullCompileSingle ac.twoRegArith k alg ac ((name,count,(LoopToWord.compHOL ctxt p labels).1),col)).2.2)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
    (complete : CompleteLoopResult result) (stepBound : LoopSteps.steps p source ≤ limit)
    (loopPremises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (gc : gcFunConstOk word.gcFun)
    (vars : everyVarHOL (fun x => decide (x < maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1))
      (compileExp (LoopToWord.compHOL ctxt p labels).1) = true)
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity r, sptLookup loc word.code = some (arity,r) → LoopBlock r)
    (wordPremises : stateRel ac k frameSize frame {word with locals := locals}
      {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false q (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL q < 2 * frame + 2 * k)
    (frameDef : frame = max (maxVarHOL q / 2 + 1 - k) (argumentCount-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize - (argumentCount-k) ≤ entry.stackSpace)
    (found : sptLookup start entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false q argumentCount k (bs,n)).1)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*limit+1))+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*limit+1))+1} 0 entry.regs)
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
      (finalFfi : HolFfiState F),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*limit+1)) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*limit+1))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*limit+1)) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  obtain ⟨block,noInstall,flat,postAlloc,wordPost,wordResult,selectedLocals,targetPost,
    wordRel,wordFfi,allocRel,targetRun,targetBound⟩ :=
    loopSequence_wordAllocated_bound ac count name alg k col p shape source sourcePost result word ctxt labels locals limit
      loopPremises complete gc vars localRel domain stepBound
  rw [← selected] at block noInstall flat postAlloc targetRun targetBound
  obtain ⟨wordComplete,wordNonerror,notTimeout⟩ := completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have targetFfi : targetPost.ffi = sourcePost.ffi := by
    have h : targetPost.ffi = wordPost.ffi := allocRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact h.trans wordFfi
  have shiftedRel : stateRel ac k frameSize frame {word with locals := locals,clock := 6*limit}
      {{entry with clock := 6*limit} with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 := by
    unfold stateRel at wordPremises ⊢
    exact ⟨rfl,wordPremises.1.2⟩
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,classification,stackRel⟩ :=
    allocatedWordSequenceRiscVWithin ac q (.block block) {word with locals := locals,clock := 6*limit} targetPost wordResult
      {entry with clock := 6*limit} k frameSize frame (sizeOf q * (6*limit+1)) lens bs bsPost n nPost compiled start argumentCount
      noInstall (by simpa using noInstallCode) (by simpa using wordCode) wordComplete notTimeout targetBound
      ⟨targetRun,wordNonerror,shiftedRel,postAlloc,flat,wordPremises.2⟩ frameDef frameSizeDef space found
      inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine
      distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  have wordOutcome := loopWordOutcome_of_resultCase ctxt word wordPost sourcePost result wordResult complete wordRel
  have correspondence := loopMachine_correspondence ac k frameSize frame lens
    {{word with locals := locals,clock := 6*limit} with clock := sizeOf q * (6*limit+1)}
    {targetPost with clock := sizeOf q * (6*limit+1) - (6*limit-targetPost.clock)}
    sourcePost stackPost result wordResult stackResult outcome finalFfi targetFfi wordOutcome
    stackRel classification events
  refine ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
  rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace,_⟩
  · exact Or.inl ⟨matching,trace⟩
  · exact Or.inr ⟨resource,trace⟩

end SteppedFlapjack.LoopToWordSteps
