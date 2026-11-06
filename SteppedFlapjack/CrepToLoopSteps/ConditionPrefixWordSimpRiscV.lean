import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceRiscV
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence

/-! Crep initialization and loops through instruction selection and RISC-V. -/
namespace SteppedFlapjack.CrepToLoopSteps
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
open SteppedFlapjack.LoopToWordSteps Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordSimp

/-- Completed Crep initialization, branch-condition loops and continuations have bounded instruction-selected RISC-V
runs, with source outcome and trace correspondence or a resource-limit prefix.
The path includes WordSimp before instruction selection but does not include the
remaining Word-to-Word optimization pipeline. The backend cost may depend on a limit-selected oracle prefix. -/
theorem branchConditionWhileBranch_wordSimp_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (temp : Nat) (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (shape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (p : CrepProgHOL 64) (pDef : p = .seq init (.seq (.while condition body) tail))
    (source sourcePost : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (crepCtxt : CrepToLoopContextExact) (live : NumSet)
    (loopProg : HolLoopProg 64) (compiledCrep : loopProg = compileHOLExact crepCtxt live p)
    (crepFactor : Nat) (crepFactorDef : crepFactor =
      1 + sizeOf (compileHOLExact crepCtxt live init) +
        (1 + (1 + sizeOf (compileHOLExact crepCtxt live (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact crepCtxt (crepCtxt.vmax+1) live condition).1) +
            sizeOf (compileHOLExact crepCtxt live body)+3) + sizeOf (compileHOLExact crepCtxt live tail)))
    (loop : LoopSemStateFiniteExact 64 F)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (locals : Spt (WordLocW 64))
    (factor : Nat) (factorDef : factor = programFactor ac temp (compileExp (LoopToWord.compHOL ctxt loopProg labels).1))
    (q : WordLangProgHOL (BitVec 64)) (selected : q = instSelect ac temp (compileExp (LoopToWord.compHOL ctxt loopProg labels).1))
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (k frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
    (complete : CompleteCrepResult result) (stepBound : CrepSteps.steps p source ≤ limit)
    (sourceRun : evalCrepSemHOLProgExact source p = (result,sourcePost))
    (sourceRel : crepToLoopStateRelExact source loop)
    (memRel : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact crepCtxt source.code loop.code)
    (localsRel : crepToLoopLocalsRelExact crepCtxt live source.locals loop.locals)
    (loopWordRel : loopToWordStateRelHOLExact loop word)
    (loopLocalsRel : LoopToWord.localsRelHOL ctxt loop.locals word.locals)
    (retLookup : sptLookup 0 word.locals = some (.loc 1 0))
    (dim : goodDimindex 64) (retLabel : ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true)
    (loopVars : ∀ k, sptMem k (accVarsHOL loopProg .ln) → sptMem k ctxt)
    (gc : gcFunConstOk word.gcFun)
    (simpFactor : Nat) (simpFactorDef : simpFactor = sizeOf (compileExp (LoopToWord.compHOL ctxt loopProg labels).1))
    (vars : everyVarHOL (fun x => decide (x < temp)) (compileExp (LoopToWord.compHOL ctxt loopProg labels).1) = true)
    (localRel : wordLocalsRel temp word.locals locals)
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity r, sptLookup loc word.code = some (arity,r) → LoopBlock r)
    (wordPremises : stateRel ac k frameSize frame {word with locals := locals}
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*(simpFactor*(6*(crepFactor*(limit+1))+1)))+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*(simpFactor*(6*(crepFactor*(limit+1))+1)))+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (factor*(simpFactor*(6*(crepFactor*(limit+1))+1))) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (factor*(simpFactor*(6*(crepFactor*(limit+1))+1)))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (factor*(simpFactor*(6*(crepFactor*(limit+1))+1))) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  subst p
  have loopShape : LoopSequenceSource loopProg := compiledCrep ▸
    branchConditionWhileBranch_wordSimpShape init initShape condition shape body tail bodyShape tailShape crepCtxt live
  obtain ⟨extra,loopPost,loopRun,loopPostRel,_,_,_,_,loopBound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition shape body tail bodyShape tailShape crepCtxt live
      source sourcePost result loop sourceRun (completeCrep_nonerror complete) sourceRel memRel globalsRel codeRel localsRel
  let loopResult := resultToLoop result
  have resultMap : loopResult = resultToLoop result := rfl
  have loopComplete : CompleteLoopResult loopResult := completeCrep_loop complete
  have loopNotError : loopResult ≠ some .error := by cases complete <;> simp [loopResult,resultToLoop]
  have shiftedRel : loopToWordStateRelHOLExact {loop with clock := loop.clock + extra}
      {word with clock := word.clock + extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  have shiftedWordPremises : stateRel ac k frameSize frame
      {word with locals := locals, clock := word.clock + extra}
      {{entry with clock := word.clock + extra} with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k q = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false q (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL q < 2 * frame + 2 * k := by
    refine ⟨?_,wordPremises.2⟩
    unfold stateRel at wordPremises ⊢
    exact ⟨rfl,wordPremises.1.2⟩
  have qRun : evaluate loopProg {loop with clock := loop.clock + extra} = (loopResult,loopPost) := by
    simpa only [compiledCrep] using loopRun
  have qBound : LoopSteps.steps loopProg {loop with clock := loop.clock + extra} ≤ crepFactor*(limit+1) := by
    rw [compiledCrep,crepFactorDef]
    exact Nat.le_trans loopBound (Nat.mul_le_mul_left _ (Nat.add_le_add_right stepBound 1))
  obtain ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩ :=
    loopSequence_wordSimp_riscvWithin ac temp loopProg loopShape {loop with clock := loop.clock + extra} loopPost loopResult
      {word with clock := word.clock + extra} ctxt labels locals factor factorDef q selected
      {entry with clock := word.clock + extra} k frameSize frame (crepFactor*(limit+1)) lens bs bsPost n nPost compiled start argumentCount
      loopComplete qBound ⟨qRun,loopNotError,shiftedRel,loopLocalsRel,retLookup,dim,retLabel,loopVars⟩
      (by simpa using gc) simpFactor simpFactorDef vars localRel noInstallCode wordCode shiftedWordPremises frameDef frameSizeDef space found inputCode anything cr c
      jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode
      pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  refine ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
  have ffiRel : sourcePost.ffi = loopPost.ffi := loopPostRel.2.2.2.2.1
  rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace⟩
  · exact Or.inl ⟨resultMap ▸ matching,trace.trans (congrArg HolFfiState.ioEvents ffiRel.symm)⟩
  · exact Or.inr ⟨resource,(congrArg HolFfiState.ioEvents ffiRel) ▸ trace⟩

end SteppedFlapjack.CrepToLoopSteps
