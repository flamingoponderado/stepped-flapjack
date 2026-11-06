import SteppedFlapjack.CrepToLoopSteps.BackendReady

/-! Compose completed Crep runs through the RISC-V backend. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A completed direct Crep run with a source step limit yields a bounded
RISC-V execution, with matching outcome and trace or a resource-limit prefix.
The backend cost includes the finite oracle prefix selected by the limit. -/
theorem directCrep_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (p : CrepProgHOL 64) (shape : DirectProgram p)
    (source sourcePost : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (crepCtxt : CrepToLoopContextExact) (live : NumSet)
    (q : HolLoopProg 64) (compiledCrep : q = compileHOLExact crepCtxt live p)
    (loop : LoopSemStateFiniteExact 64 F)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (k frameSize frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64) (start argumentCount : Nat)
    (complete : CompleteCrepResult result) (stepBound : CrepSteps.steps p source ≤ limit)
    (sourceRun : evalCrepSemHOLProgExact source p = (result,sourcePost))
    (sourceRel : crepToLoopStateRelExact source loop)
    (memRel : crepToLoopMemRelHOLExact source.memory loop.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals loop.globals)
    (codeRel : crepToLoopCodeRelExact crepCtxt source.code loop.code)
    (localsRel : crepToLoopLocalsRelExact crepCtxt live source.locals loop.locals)
    (loopWordRel : loopToWordStateRelHOLExact loop word)
    (wordLocalsRel : LoopToWord.localsRelHOL ctxt loop.locals word.locals)
    (retLookup : sptLookup 0 word.locals = some (.loc 1 0))
    (dim : goodDimindex 64) (retLabel : ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true)
    (vars : ∀ k, sptMem k (accVarsHOL q .ln) → sptMem k ctxt)
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
    (wordPremises : stateRel ac k frameSize frame word {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt q labels).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt q labels).1 = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false (LoopToWord.compHOL ctxt q labels).1 (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt q labels).1 < 2*frame+2*k)
    (frameDef : frame = max (maxVarHOL (LoopToWord.compHOL ctxt q labels).1 / 2 + 1 - k) (argumentCount-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (space : frameSize - (argumentCount-k) ≤ entry.stackSpace)
    (found : sptLookup start entry.code = some
      (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false (LoopToWord.compHOL ctxt q labels).1 argumentCount k (bs,n)).1)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (2*limit)+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (2*limit)+1} 0 entry.regs)
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
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (2*limit) entry.code (LoopToWord.compHOL ctxt q labels).1 (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (2*limit)+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (2*limit) entry.code (LoopToWord.compHOL ctxt q labels).1 (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = sourcePost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: sourcePost.ffi.ioEvents)) := by
  have qShape : StackReady q := compiledCrep ▸ compile_stackReady shape crepCtxt live
  obtain ⟨extra,loopResult,loopPost,loopRun,loopPostRel,_,_,_,resultMap,_,loopBound⟩ :=
    directProgram_correct_with_steps shape source result sourcePost loop crepCtxt live sourceRun
      (completeCrep_nonerror complete) sourceRel memRel globalsRel codeRel localsRel
  have loopComplete : CompleteLoopResult loopResult := resultMap ▸ completeCrep_loop complete
  have loopNotError : loopResult ≠ some .error := by cases loopComplete <;> simp
  have shiftedRel : loopToWordStateRelHOLExact {loop with clock := loop.clock + extra}
      {word with clock := word.clock + extra} := by
    rcases loopWordRel with ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    refine ⟨len,hm,hd,hs,?_,hbe,hffi,hbase,hlen,htop,hg,hcode⟩
    simp only
    omega
  have shiftedWordPremises : stateRel ac k frameSize frame {word with clock := word.clock + extra}
      {{entry with clock := word.clock + extra} with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt q labels).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt q labels).1 = true ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false (LoopToWord.compHOL ctxt q labels).1 (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt q labels).1 < 2*frame+2*k := by
    refine ⟨?_,wordPremises.2⟩
    unfold stateRel at wordPremises ⊢
    exact ⟨rfl,wordPremises.1.2⟩
  have qRun : evaluate q {loop with clock := loop.clock + extra} = (loopResult,loopPost) := by
    simpa only [compiledCrep] using loopRun
  have qBound : LoopSteps.steps q {loop with clock := loop.clock + extra} ≤ 2*limit := by
    rw [compiledCrep]
    omega
  obtain ⟨outcome,ticks,finalMachine,finalFfi,stackPost,stackResult,tickBound,machineRun,
    events,classification,wordPost,wordResult,wordRun,wordFfi,wordRelation,stackRelation,correspondence⟩ :=
    stackReady_riscvWithin ac q qShape {loop with clock := loop.clock + extra} loopPost loopResult
      {word with clock := word.clock + extra} {entry with clock := word.clock + extra} ctxt labels
      k frameSize frame (2*limit) lens bs bsPost n nPost compiled start argumentCount loopComplete qBound
      ⟨qRun,loopNotError,shiftedRel,wordLocalsRel,retLookup,dim,retLabel,vars⟩ noInstallCode wordCode
      shiftedWordPremises frameDef frameSizeDef space found inputCode anything cr c jump bounds pointer f gen
      maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation
      ha hs hk hf hcode hor rel hpc hmc tie machineRel
  refine ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
  have ffiRel : sourcePost.ffi = loopPost.ffi := loopPostRel.2.2.2.2.1
  rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace,_⟩
  · left
    exact ⟨resultMap ▸ matching, trace.trans (congrArg HolFfiState.ioEvents ffiRel.symm)⟩
  · right
    exact ⟨resource, (congrArg HolFfiState.ioEvents ffiRel) ▸ trace⟩

end SteppedFlapjack.CrepToLoopSteps
