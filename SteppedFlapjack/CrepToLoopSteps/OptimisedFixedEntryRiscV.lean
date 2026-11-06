import SteppedFlapjack.CrepToLoopSteps.SimpFixed
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.LoopToWordSteps.FixedEntryRiscV
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
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordAllocSteps Flapjack.WordToStackProofs.InitializationStateRel

/-- A completed Crep run bounds actual fully allocated Word-to-RISC-V execution. -/
theorem branchConditionWhileBranch_optimised_fixedEntry_riscvWithin {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name k : Nat) (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (shape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (p : CrepProgHOL 64) (pDef : p = .seq init (.seq (.while condition body) tail))
    (source sourcePost : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (crepCtxt : CrepToLoopContextExact) (live : NumSet)
    (loopProg : HolLoopProg 64) (compiledCrep : loopProg = optimiseHOL (compileHOLExact crepCtxt live (crepSimpProgHOL p)))
    (crepFactor : Nat) (crepFactorDef : crepFactor =
      1 + sizeOf (compileHOLExact crepCtxt live init) +
        (1 + (1 + sizeOf (compileHOLExact crepCtxt live (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact crepCtxt (crepCtxt.vmax+1) live condition).1) +
            sizeOf (compileHOLExact crepCtxt live body)+3) + sizeOf (compileHOLExact crepCtxt live tail)))
    (loop : LoopSemStateFiniteExact 64 F)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ctxt : Spt Nat) (labels : Nat × Nat)
    (member : (name,1,(LoopToWord.compHOL ctxt loopProg labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (q : WordLangProgHOL (BitVec 64))
    (kDef : k = ac.regCount-(5+ac.avoidRegs.length))
    (selected : q = (fullCompileSingle ac.twoRegArith k wc.regAlg ac ((name,1,(LoopToWord.compHOL ctxt loopProg labels).1),entryColour wc programs name)).2.2)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : entry.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false (compile wc ac programs).2).1.IsPrefix entry.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) entry coracle)
    (frameSize frame limit : Nat)
    (wordDef : word = WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k entry (sptFromAList (compile wc ac programs).2) coracle))
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
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity r, sptLookup loc word.code = some (arity,r) → LoopBlock r)
    (frameDef : frame = max (maxVarHOL q / 2 + 1 - k) (1-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize ≤ entry.stackSpace)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1))+1))+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1))+1))+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1))+1)) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl name) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1))+1))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1))+1)) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  subst p
  have fixed := branchConditionWhileBranch_simp_fixed init initShape condition shape body tail bodyShape tailShape
  rw [fixed] at compiledCrep
  have rawShape := branchConditionWhileBranch_wordSimpShape init initShape condition shape body tail bodyShape tailShape crepCtxt live
  have loopShape : LoopSequenceSource loopProg := compiledCrep ▸ LoopLiveSteps.optimise_sequence rawShape
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
  have shiftedWordDef : {word with clock := word.clock + extra} =
      WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k {entry with clock := word.clock+extra}
          (sptFromAList (compile wc ac programs).2) coracle) := by
    rw [wordDef]
    rfl
  obtain ⟨optimizedRun,_,optimizedBound⟩ := LoopLiveSteps.optimise_complete_source_steps rawShape
    {loop with clock := loop.clock+extra} loopPost loopResult loopRun loopComplete
  have qRun : evaluate loopProg {loop with clock := loop.clock + extra} = (loopResult,loopPost) := by
    simpa only [compiledCrep] using optimizedRun
  have rawBound : LoopSteps.steps (compileHOLExact crepCtxt live (.seq init (.seq (.while condition body) tail)))
      {loop with clock := loop.clock+extra} ≤ crepFactor*(limit+1) := by
    rw [crepFactorDef]
    exact loopBound.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right stepBound 1))
  have qBound : LoopSteps.steps loopProg {loop with clock := loop.clock + extra} ≤ sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1) := by
    rw [compiledCrep]
    exact optimizedBound.trans (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨bs,n,outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩ :=
    loopSequence_fixedEntry_riscvWithin wc ac programs name loopProg loopShape {loop with clock := loop.clock + extra} loopPost loopResult
      ctxt labels member nodup noRaise noStore {entry with clock := word.clock + extra} coracle
      (by simpa using codeEq) (by simpa using bitmapsPrefix) (by simpa [initStateOk] using ok)
      q k frameSize frame (sizeOf loopProg * (2 * (crepFactor*(limit+1)) + 1)) kDef selected frameDef frameSizeDef (by simpa using space)
      {word with clock := word.clock+extra} shiftedWordDef loopComplete qBound
      ⟨qRun,loopNotError,shiftedRel,loopLocalsRel,retLookup,dim,retLabel,loopVars⟩
      (by simpa using gc) (by simpa using noInstallCode) (by simpa using wordCode)
      inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine
      distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  refine ⟨bs,n,outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
  have ffiRel : sourcePost.ffi = loopPost.ffi := loopPostRel.2.2.2.2.1
  rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace⟩
  · exact Or.inl ⟨resultMap ▸ matching,trace.trans (congrArg HolFfiState.ioEvents ffiRel.symm)⟩
  · exact Or.inr ⟨resource,(congrArg HolFfiState.ioEvents ffiRel) ▸ trace⟩

end SteppedFlapjack.CrepToLoopSteps
