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

end SteppedFlapjack.WordToStackSteps
