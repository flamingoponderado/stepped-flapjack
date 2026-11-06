import SteppedFlapjack.LoopToWordSteps.WordAllocatedRiscV
import SteppedFlapjack.LoopToWordSteps.WordAllocatedSequence
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.FixedEntryFrame

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

open SteppedFlapjack.WordAllocSteps
open Flapjack.WordToStackProofs.InitializationStateRel

/-- A completed Loop execution induces a bounded RISC-V run for the actual
whole-program entry when its compiler-selected frame fits. -/
theorem loopSequence_fixedEntry_riscvWithin {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name : Nat) (p : HolLoopProg 64) (shape : LoopSequenceSource p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (ctxt : Spt Nat) (labels : Nat × Nat)
    (member : (name,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : entry.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false (compile wc ac programs).2).1.IsPrefix entry.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) entry coracle)
    (q : WordLangProgHOL (BitVec 64)) (k frameSize frame limit : Nat)
    (kDef : k = ac.regCount-(5+ac.avoidRegs.length))
    (qDef : q = (fullCompileSingle ac.twoRegArith k wc.regAlg ac
      ((name,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs name)).2.2)
    (frameDef : frame = max (maxVarHOL q / 2 + 1 - k) (1-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize ≤ entry.stackSpace)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordDef : word = WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k entry (sptFromAList (compile wc ac programs).2) coracle))
    (complete : CompleteLoopResult result) (stepBound : LoopSteps.steps p source ≤ limit)
    (loopPremises : evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ key, sptMem key (accVarsHOL p .ln) → sptMem key ctxt))
    (gc : gcFunConstOk word.gcFun)
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity r, sptLookup loc word.code = some (arity,r) → LoopBlock r)
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
    (hpc : LabSem.locToPc name 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ (bs : AppList (BitVec 64)) (n : Nat) (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*limit+1)) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl name) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*limit+1))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*limit+1)) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome result outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  subst k
  have nameMember : name ∈ programs.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
  have notRaise : name ≠ raiseStubLocation := by intro h; subst name; exact noRaise nameMember
  have notStore : name ≠ storeConstsStubLocation := by intro h; subst name; exact noStore nameMember
  have wordShape := loopSequenceSource_word shape ctxt labels
  have actual := wholeWordStack_entryColour_simulation_inputs wc ac programs name 1
    (LoopToWord.compHOL ctxt p labels).1 member nodup notRaise notStore wordShape
  rw [← qDef] at actual
  obtain ⟨bs,n,bsPost,nPost,compiled,actualFrame,actualSize,_,_,_,_,actualFrameDef,actualSizeDef,
    compilation,_,found,bitmapLength,bitmapBound,bitmapPrefix⟩ := actual
  have frameEq : actualFrame = frame := actualFrameDef.trans frameDef.symm
  rw [frameEq] at actualSizeDef compilation
  have sizeEq : actualSize = frameSize := actualSizeDef.trans frameSizeDef.symm
  rw [sizeEq] at compilation
  rw [← codeEq] at found
  have bitmapBound : n-(appListAppend bs).length ≤ entry.bitmaps.length := bitmapBound.trans bitmapsPrefix.length_le
  have bitmapPrefix : (appListAppend bsPost).IsPrefix (entry.bitmaps.drop (n-(appListAppend bs).length)) :=
    bitmapPrefix.trans (bitmapsPrefix.drop _)
  have kBound : 1 ≤ ac.regCount-(5+ac.avoidRegs.length) := by have h := ok.1; omega
  have argSpace : 1-(ac.regCount-(5+ac.avoidRegs.length)) = 0 := by omega
  have frameShape : if frame = 0 then frameSize = 0 else frameSize = frame+1 := by split <;> simp_all
  have related := wholeWordStack_initialFrame wc ac programs entry coracle noRaise noStore codeEq bitmapsPrefix ok frameSize frame frameShape space
  dsimp only at related
  rw [← wordDef] at related
  have entryDomain : sptDomain word.locals = (fun key => key ∈ evenList 1) := by
    rw [wordDef]
    exact (nativeEntry_locals _ frameSize 0).1
  have localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt p labels).1)+1) word.locals word.locals := fun _ _ => rfl
  obtain ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩ :=
    loopSequence_wordAllocated_riscvWithin ac 1 name wc.regAlg (ac.regCount-(5+ac.avoidRegs.length)) (entryColour wc programs name)
      p shape source sourcePost result word ctxt labels word.locals q qDef entry frameSize frame limit [] bs bsPost n nPost compiled name 1
      complete stepBound loopPremises gc localRel entryDomain noInstallCode wordCode
      ⟨by simpa only [argSpace,Nat.sub_zero] using related,compilation,bitmapLength,bitmapBound,bitmapPrefix⟩
      frameDef frameSizeDef (by simpa only [argSpace,Nat.sub_zero] using space) found
      inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine
      distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  exact ⟨bs,n,outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩

end SteppedFlapjack.LoopToWordSteps
