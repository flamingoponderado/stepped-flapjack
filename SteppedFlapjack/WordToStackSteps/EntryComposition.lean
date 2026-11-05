import SteppedFlapjack.WordToStackSteps.CallSequenceCost
import SteppedFlapjack.StackToLabSteps.RiscVPipeline

/-! Connect bounded Word-to-Stack executions to StackSem entry calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps

/-- Source outcomes that correspond to complete top-level executions. -/
inductive CompleteWordResult : Option (WordSemResult 64) → Prop
  | return (values) : CompleteWordResult (some (.result (.loc 1 0) values))
  | resource : CompleteWordResult (some .notEnoughSpace)
  | ffi (event) : CompleteWordResult (some (.finalFfi event))

/-- The compiler result relation maps a complete source outcome to either its
matching target outcome or the compiler's stack-resource outcome. -/
theorem completeWordResult_target {C F : Type} (ac : AsmConfigExact 64) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × C) F)
    (targetPost : StackSemStateFiniteExact 64 C F) (result : Option (WordSemResult 64))
    (targetResult : Option (StackSemResult 64)) (lens : List Nat)
    (complete : CompleteWordResult result)
    (relation : compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens) :
    ∃ outcome, stackEntryClass targetResult = .CompleteResult outcome := by
  classical
  unfold compCorrectResult at relation
  split at relation
  · rw [relation.1]
    exact ⟨HolOutcome.resourceLimitHit, by simp [stackEntryClass]⟩
  · rename_i matchResult
    have eq : result.map compileResult = targetResult := by simpa using matchResult
    rw [← eq]
    cases complete <;> simp [compileResult,stackEntryClass]

/-- An actual completed body run lifts through the native tail entry call,
adding exactly one StackSem step. -/
theorem completedBody_entry {C F : Type} (entry : StackSemStateFiniteExact 64 C F)
    (start limit : Nat) (body : HolProg 64) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 C F) (outcome : HolOutcome) (bound : Nat)
    (found : sptLookup start entry.code = some body)
    (run : StackSemEvaluate.evaluate (body,{entry with clock := limit}) = (result,post))
    (complete : stackEntryClass result = .CompleteResult outcome)
    (cost : steps (body,{entry with clock := limit}) ≤ bound) :
    StackSemEvaluate.evaluate (.call none (.inl start) none,{entry with clock := limit+1}) = (result,post) ∧
    result ≠ some .error ∧
    steps (.call none (.inl start) none,{entry with clock := limit+1}) ≤ 1+bound := by
  have good : badFunReturn result = false := by
    cases result with
    | none => simp [stackEntryClass] at complete
    | some r => cases r <;> simp_all [stackEntryClass,badFunReturn]
  have nerr : result ≠ some .error := by
    intro bad
    subst result
    simp [stackEntryClass] at complete
  refine ⟨?_,nerr,?_⟩
  · rw [StackSemEvaluate.evaluate_call]
    simp only [findCode,found,Nat.add_one_ne_zero, ↓reduceIte,StackSemEvaluateClock.fixClockEvaluate]
    simp only [decClock,Nat.add_sub_cancel]
    rw [run]
    simp [good]
  · rw [steps_call_none]
    simp only [findCode,found,Nat.add_one_ne_zero, ↓reduceIte]
    simpa [decClock] using Nat.add_le_add_left cost 1


/-- A compiled function's successful stack-allocation prefix adds two steps
before executing its body. -/
theorem allocatedBody_entry {C F : Type} (entry : StackSemStateFiniteExact 64 C F)
    (start limit allocation : Nat) (body : HolProg 64) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 C F) (outcome : HolOutcome) (bound : Nat)
    (found : sptLookup start entry.code = some (.seq (.stackAlloc allocation) body))
    (enabled : entry.useStack = true) (space : allocation ≤ entry.stackSpace)
    (run : StackSemEvaluate.evaluate (body,{entry with stackSpace := entry.stackSpace-allocation, clock := limit}) = (result,post))
    (complete : stackEntryClass result = .CompleteResult outcome)
    (cost : steps (body,{entry with stackSpace := entry.stackSpace-allocation, clock := limit}) ≤ bound) :
    StackSemEvaluate.evaluate (.call none (.inl start) none,{entry with clock := limit+1}) = (result,post) ∧
    result ≠ some .error ∧
    steps (.call none (.inl start) none,{entry with clock := limit+1}) ≤ 3+bound := by
  have allocationRun : StackSemEvaluate.evaluate (.stackAlloc allocation,{entry with clock := limit}) =
      (none,{entry with stackSpace := entry.stackSpace-allocation, clock := limit}) := by
    rw [StackSemEvaluate.evaluate_stackAlloc]
    simp [enabled,Nat.not_lt.mpr space]
  have wholeRun : StackSemEvaluate.evaluate (.seq (.stackAlloc allocation) body,{entry with clock := limit}) = (result,post) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,allocationRun]
    exact run
  have allocationCost : steps (.stackAlloc allocation,{entry with clock := limit}) = 1 := by
    exact steps_leaf _ _ rfl
  have wholeCost : steps (.seq (.stackAlloc allocation) body,{entry with clock := limit}) ≤ 2+bound := by
    rw [steps_seq,StackSemEvaluateClock.fixClockEvaluate,allocationRun,allocationCost]
    simp only
    omega
  have wrapped := completedBody_entry entry start limit (.seq (.stackAlloc allocation) body)
    result post outcome (2+bound) found wholeRun complete wholeCost
  rcases wrapped with ⟨entryRun,notError,entryCost⟩
  exact ⟨entryRun,notError,by omega⟩

/-- Insufficient entry stack space is a completed resource outcome. -/
theorem allocationFailure_entry {C F : Type} (entry : StackSemStateFiniteExact 64 C F)
    (start limit allocation : Nat) (body : HolProg 64)
    (found : sptLookup start entry.code = some (.seq (.stackAlloc allocation) body))
    (enabled : entry.useStack = true) (space : entry.stackSpace < allocation) :
    ∃ post, StackSemEvaluate.evaluate (.call none (.inl start) none,{entry with clock := limit+1}) =
        (some (.halt (.word 2)),post) ∧
      stackEntryClass (some (.halt (.word 2)) : Option (StackSemResult 64)) = .CompleteResult HolOutcome.resourceLimitHit ∧
      post.ffi = entry.ffi ∧
      steps (.call none (.inl start) none,{entry with clock := limit+1}) ≤ 3 := by
  let post := StackSemStateOps.emptyEnv {entry with clock := limit}
  have allocationRun : StackSemEvaluate.evaluate (.stackAlloc allocation,{entry with clock := limit}) =
      (some (.halt (.word 2)),post) := by
    rw [StackSemEvaluate.evaluate_stackAlloc]
    simp [enabled,space,post]
  have bodyRun : StackSemEvaluate.evaluate (.seq (.stackAlloc allocation) body,{entry with clock := limit}) =
      (some (.halt (.word 2)),post) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,allocationRun]
  have bodyCost : steps (.seq (.stackAlloc allocation) body,{entry with clock := limit}) ≤ 2 := by
    rw [steps_seq,StackSemEvaluateClock.fixClockEvaluate,allocationRun,steps_leaf _ _ rfl]
    simp
  have classified : stackEntryClass (some (.halt (.word 2)) : Option (StackSemResult 64)) = .CompleteResult HolOutcome.resourceLimitHit := by simp [stackEntryClass]
  obtain ⟨run,_,bound⟩ := completedBody_entry entry start limit (.seq (.stackAlloc allocation) body)
    (some (.halt (.word 2))) post HolOutcome.resourceLimitHit 2 found bodyRun classified bodyCost
  exact ⟨post,run,classified,rfl,by omega⟩

/-- A bounded Word call sequence whose compiled body is the StackSem entry
is carried through the existing backend to an actual bounded RISC-V run. -/
theorem wordSequenceRiscVWithin {F : Type}
    (ac : AsmConfigExact 64) (program : WordLangProgHOL (BitVec 64)) (shape : CallSequence program)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordResult : Option (WordSemResult 64)) (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start : Nat)
    (noInstall : noInstallSubprogsHOL program = true) (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
    (complete : CompleteWordResult wordResult) (notTimeout : wordResult ≠ some .timeOut)
    (stepBound : WordSteps.steps program word ≤ limit)
    (wordPremises : WordSemStateFiniteExact.evaluate program word = (wordResult,wordPost) ∧
      wordResult ≠ some .error ∧ stateRel ac k frameSize frame word entry lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false program (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k)
    (found : sptLookup start entry.code = some compiled)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (1 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (1 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      compCorrectResult ac k frameSize frame {word with clock := limit}
        {wordPost with clock := limit - (word.clock - wordPost.clock)} stackPost wordResult stackResult lens := by
  obtain ⟨stackPost,stackResult,bodyRun,bodyRelation,bodyBound⟩ :=
    callSequence_bounded ac program shape word wordPost entry wordResult k frameSize frame bs bsPost n nPost limit
      compiled lens noInstall noInstallCode wordCode notTimeout stepBound wordPremises
  obtain ⟨outcome,classification⟩ := completeWordResult_target ac k frameSize frame _ _ stackPost wordResult stackResult lens complete bodyRelation
  obtain ⟨entryRun,entryNonError,entryBound⟩ := completedBody_entry entry start limit compiled stackResult stackPost outcome _ found bodyRun classification bodyBound
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
    stackPipelineRiscVWithin inputCode entry start (limit+1) (1 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))
      stackResult stackPost anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab outcome
      pc mc labCode labs asm machine distinct sourceCode entryRun entryNonError entryBound pre relation ha hs hk hf hcode hor rel hpc classification hmc tie machineRel
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,bodyRelation⟩


/-- The same Word-to-RISC-V bound using the real compiled-function allocation prefix. -/
theorem allocatedWordSequenceRiscVWithin {F : Type}
    (ac : AsmConfigExact 64) (program : WordLangProgHOL (BitVec 64)) (shape : CallSequence program)
    (word wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (wordResult : Option (WordSemResult 64)) (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
    (noInstall : noInstallSubprogsHOL program = true) (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
    (complete : CompleteWordResult wordResult) (notTimeout : wordResult ≠ some .timeOut)
    (stepBound : WordSteps.steps program word ≤ limit)
    (wordPremises : WordSemStateFiniteExact.evaluate program word = (wordResult,wordPost) ∧
      wordResult ≠ some .error ∧ stateRel ac k frameSize frame word {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false program (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k)
    (frameDef : frame = max (maxVarHOL program / 2 + 1 - k) (argumentCount-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize - (argumentCount-k) ≤ entry.stackSpace)
    (found : sptLookup start entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false program argumentCount k (bs,n)).1)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧
      compCorrectResult ac k frameSize frame {word with clock := limit}
        {wordPost with clock := limit - (word.clock - wordPost.clock)} stackPost wordResult stackResult lens := by
  obtain ⟨stackPost,stackResult,bodyRun,bodyRelation,bodyBound⟩ :=
    callSequence_bounded ac program shape word wordPost {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} wordResult k frameSize frame bs bsPost n nPost limit
      compiled lens noInstall noInstallCode wordCode notTimeout stepBound wordPremises
  obtain ⟨outcome,classification⟩ := completeWordResult_target ac k frameSize frame _ _ stackPost wordResult stackResult lens complete bodyRelation
  have enabled : entry.useStack = true := wordPremises.2.2.1.2.2.2.2.1
  have foundBody : sptLookup start entry.code = some (.seq (.stackAlloc (frameSize - (argumentCount-k))) compiled) := by
    have compilation := wordPremises.2.2.2.2.2.1
    simp only [Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative, ← frameDef, ← frameSizeDef, compilation] at found
    exact found
  obtain ⟨entryRun,entryNonError,entryBound⟩ := allocatedBody_entry entry start limit (frameSize - (argumentCount-k)) compiled stackResult stackPost outcome _ foundBody enabled space bodyRun classification bodyBound
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
    stackPipelineRiscVWithin inputCode entry start (limit+1) (3 + callSequenceCost ac limit entry.code program (bs,n) (k,frameSize,frame))
      stackResult stackPost anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab outcome
      pc mc labCode labs asm machine distinct sourceCode entryRun entryNonError entryBound pre relation ha hs hk hf hcode hor rel hpc classification hmc tie machineRel
  exact ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,events,bodyRelation⟩



/-- Even when the compiled entry frame does not fit, the backend produces an
actual RISC-V resource-limit outcome with a fixed three-step StackSem bound. -/
theorem allocationFailureRiscVWithin {F : Type}
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F) (start limit allocation : Nat) (body : HolProg 64)
    (found : sptLookup start entry.code = some (.seq (.stackAlloc allocation) body))
    (enabled : entry.useStack = true) (space : entry.stackSpace < allocation)
    (inputCode : List (Nat × HolProg 64))
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : entry.code = sptFromAList inputCode)
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds (uniformFactor (width := 64) c * 3)
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * 3) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt HolOutcome.resourceLimitHit,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = entry.ffi.ioEvents := by
  obtain ⟨post,run,classification,postFfi,stepBound⟩ := allocationFailure_entry entry start limit allocation body found enabled space
  obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
    stackPipelineRiscVWithin inputCode entry start (limit+1) 3 (some (.halt (.word 2))) post
      anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab HolOutcome.resourceLimitHit
      pc mc labCode labs asm machine distinct sourceCode run (by simp) stepBound pre relation ha hs hk hf hcode hor rel hpc classification hmc tie machineRel
  have postEvents : post.ffi.ioEvents = entry.ffi.ioEvents := by rw [postFfi]
  exact ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events.trans postEvents⟩

end SteppedFlapjack.WordToStackSteps
