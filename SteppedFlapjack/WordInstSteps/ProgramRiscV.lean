import SteppedFlapjack.WordInstSteps.Compositional
import SteppedFlapjack.WordToStackSteps.EntryComposition

/-! Compositional Word instruction selection through RISC-V. -/
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.Compiler.Backend.WordInst Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps

/-- A completed compositional Word source run yields an actual bounded RISC-V
run after instruction selection and the proved backend compilation. -/
theorem boundedProgram_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (p : WordLangProgHOL (BitVec 64))
    (factor : Nat) (shape : BoundedProgram ac temp p factor)
    (q : WordLangProgHOL (BitVec 64)) (selected : q = instSelect ac temp p)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (result : Option (WordSemResult 64)) (locals : Spt (WordLocW 64))
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
    (complete : CompleteWordResult result) (sourceBound : WordSteps.steps p source ≤ limit)
    (sourceRun : evaluate p source = (result,sourcePost))
    (vars : everyVarHOL (fun x => decide (x < temp)) p = true)
    (localRel : wordLocalsRel temp source.locals locals)
    (noInstallCode : WordProps.noInstallCode source.code)
    (wordCode : ∀ loc arity r, sptLookup loc source.code = some (arity,r) → LoopBlock r)
    (wordPremises : stateRel ac k frameSize frame {source with locals := locals}
      {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k q = true ∧
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*limit)+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*limit)+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (factor*limit) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*limit)+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (factor*limit) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ localsPost,
        evaluate q {source with locals := locals} = (result,{sourcePost with locals := localsPost}) ∧
        compCorrectResult ac k frameSize frame {source with locals := locals, clock := factor*limit}
          {sourcePost with locals := localsPost, clock := factor*limit - (source.clock - sourcePost.clock)}
          stackPost result stackResult lens := by
  have nonerror : result ≠ some .error := by cases complete <;> simp
  have notTimeout : result ≠ some .timeOut := by cases complete <;> simp
  obtain ⟨localsPost,selectedRun,_⟩ := inst_select_thm ac temp p source result sourcePost locals
    ⟨sourceRun,vars,nonerror,localRel⟩
  have selectedBound := boundedProgram_steps (C := Nat × LabToTarget.Config) (F := F) ac temp shape
    source sourcePost result locals sourceRun nonerror vars localRel
  have qBound : WordSteps.steps q {source with locals := locals} ≤ factor * limit := by
    rw [selected]
    exact Nat.le_trans selectedBound (Nat.mul_le_mul_left _ sourceBound)
  have qShape : CallSequence q := .block (selected ▸ boundedProgram_block ac temp shape)
  have qNoInstall : noInstallSubprogsHOL q = true := selected ▸ (boundedProgram_conventions ac temp shape).2
  have qFlat : flatExpConventions q = true := selected ▸ (boundedProgram_conventions ac temp shape).1
  have qRun : evaluate q {source with locals := locals} = (result,{sourcePost with locals := localsPost}) := by
    simpa only [selected] using selectedRun
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,
    classification,stackRel⟩ :=
    allocatedWordSequenceRiscVWithin ac q qShape {source with locals := locals} {sourcePost with locals := localsPost}
      result entry k frameSize frame (factor*limit) lens bs bsPost n nPost compiled start argumentCount
      qNoInstall noInstallCode wordCode complete notTimeout qBound
      ⟨qRun,nonerror,wordPremises.1,wordPremises.2.1,qFlat,wordPremises.2.2⟩
      frameDef frameSizeDef space found inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput
      oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor
      rel hpc hmc tie machineRel
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,
    classification,localsPost,qRun,stackRel⟩

end SteppedFlapjack.WordInstSteps
