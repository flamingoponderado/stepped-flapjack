import SteppedFlapjack.PanToCrepSteps.ConditionBranchWhile
import SteppedFlapjack.PanToCrepSteps.WhileRiscV
import SteppedFlapjack.CrepToLoopSteps.OptimisedFixedEntryRiscV
import SteppedFlapjack.WordToStackSteps.FixedEntryFrame
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import SteppedFlapjack.CrepToLoopSteps.BackendReady
import SteppedFlapjack.LoopToWordSteps.SelectedRiscV

/-! Pancake loops followed by branches through RISC-V. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Pancake.PanLang SteppedFlapjack.CrepToLoopSteps
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

/-- A completed Pancake initialization, loop and continuation bounds the RISC-V run through the complete Word compiler, with outcome and trace correspondence or a resource-limit prefix. -/
theorem panBranchConditionWhileBranch_optimised_allFrames_riscvWithin {F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (name k : Nat)
    (panInit : ProgHOL 64) (panCondition : ExpHOL 64) (panBody panTail : ProgHOL 64) (panContext : PanToCrepContextExact 64)
    (panInitShape : PanToCrepSteps.BranchProgram panContext panInit)
    (panShape : PanToCrepSteps.BranchCondition panContext panCondition) (panBodyShape : PanToCrepSteps.BranchProgram panContext panBody)
    (panTailShape : PanToCrepSteps.BranchProgram panContext panTail)
    (pan panPost : PanSemStateFiniteExact 64 F) (panResult : Option (PanSemResultExact 64))
    (panComplete : CompletePanResult panResult)
    (panRun : pan.evaluateHOLFiniteState (.seq panInit (.seq (.while panCondition panBody) panTail)) = (panResult,panPost))
    (panLocalised : localisedProgHOL (.seq panInit (.seq (.while panCondition panBody) panTail)) = true)
    (source : CrepSemHOLState 64 F)
    (panStateRel : panToCrepStateRelFiniteExact pan source)
    (panCodeRel : codeRelExactHOLW panContext pan.code source.code)
    (panExcpRel : panToCrepExcpRelFiniteExact panContext.eids pan.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact panContext pan.locals source.locals)
    (init : CrepProgHOL 64) (initDef : init = compileProgExactHOLW panContext panInit)
    (condition : CrepExpHOL 64)
    (conditionDef : compileExpExactHOLW panContext panCondition = ([condition],.one))
    (body : CrepProgHOL 64) (bodyDef : body = compileProgExactHOLW panContext panBody)
    (tail : CrepProgHOL 64) (tailDef : tail = compileProgExactHOLW panContext panTail)
    (p : CrepProgHOL 64) (pDef : p = compileProgExactHOLW panContext (.seq panInit (.seq (.while panCondition panBody) panTail)))
    (panFactor : Nat) (panFactorDef : panFactor = 3 + sizeOf (compileProgExactHOLW panContext panInit) + sizeOf (compileProgExactHOLW panContext panBody) +
      sizeOf (compileProgExactHOLW panContext panTail))
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
    (stepBound : controlSteps (.seq panInit (.seq (.while panCondition panBody) panTail)) pan ≤ limit)
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1))+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1))+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc name 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ (result : Option (CrepResultHOLExact 64)) (sourcePost : CrepSemHOLState 64 F),
      pcCompileCorrectResultRel panContext panPost sourcePost panResult result ∧
      ((∃ (bs : AppList (BitVec 64)) (n : Nat) (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1)) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl name) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1)) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = panPost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: panPost.ffi.ioEvents))) ∨
      (∃ (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
        ticks ≤ labTickBound 4 labCode lab.codeBuffer *
          (flattenStepFactor * (computedRunCost bounds (uniformFactor (width := 64) c * 3)
            (.call none (.inl name) none)
            (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1))+1} 0 entry.regs) *
            (uniformFactor (width := 64) c * 3) + 4)) ∧
        evaluateTargetHOL mc lab.ffi ticks machine = (.halt HolOutcome.resourceLimitHit,finalMachine,finalFfi) ∧
        finalFfi.ioEvents <+: panPost.ffi.ioEvents)) := by
  have nonerror : panResult ≠ some .error := by cases panComplete <;> simp
  have correct : pcCompileCorrectAt (.seq panInit (.seq (.while panCondition panBody) panTail)) pan :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨result,sourcePost,sourceRun,postRel,_,_,resultRel⟩ :=
    correct panResult panPost source panContext panRun nonerror panStateRel panCodeRel panExcpRel panLocalsRel panLocalised
  have crepBound := branchConditionWhileBranch_compiled_steps panInit panCondition panBody panTail panContext panInitShape panShape
    panBodyShape panTailShape pan panPost panResult source panRun nonerror panStateRel panCodeRel panExcpRel panLocalsRel panLocalised
  obtain ⟨ce,ceCompiled,direct⟩ := branchCondition_compile panShape
  rw [conditionDef] at ceCompiled
  cases ceCompiled
  have initEq : CrepToLoopSteps.BranchProgram init := initDef ▸ branch_compile panInitShape
  have bodyEq : CrepToLoopSteps.BranchProgram body := bodyDef ▸ branch_compile panBodyShape
  have tailEq : CrepToLoopSteps.BranchProgram tail := tailDef ▸ branch_compile panTailShape
  have pWhile : p = .seq init (.seq (.while condition body) tail) := by
    rw [pDef]
    simp [compileProgExactHOLW,compileWhileExactHOLW,conditionDef,initDef,bodyDef,tailDef]
  have complete : CompleteCrepResult result := by
    cases panComplete with
    | «return» value =>
      simp only [pcCompileCorrectResultRel] at resultRel
      rw [resultRel]
      exact .return _
    | ffi event =>
      simp only [pcCompileCorrectResultRel] at resultRel
      rw [resultRel]
      exact .ffi _
  have crepLimit : CrepSteps.steps p source ≤ panFactor*limit := by
    rw [pDef,panFactorDef]
    exact Nat.le_trans crepBound (Nat.mul_le_mul_left _ stepBound)
  refine ⟨result,sourcePost,resultRel,?_⟩
  by_cases space : frameSize ≤ entry.stackSpace
  · left
    obtain ⟨bs,n,outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩ :=
      branchConditionWhileBranch_optimised_fixedEntry_riscvWithin wc ac programs name k init initEq condition direct body tail bodyEq tailEq p pWhile source sourcePost result
        crepCtxt live loopProg compiledCrep crepFactor crepFactorDef loop word ctxt labels member nodup noRaise noStore q kDef selected
        entry coracle codeEq bitmapsPrefix ok frameSize frame (panFactor*limit) wordDef complete crepLimit
        (by simpa [pDef] using sourceRun) sourceRel memRel globalsRel codeRel localsRel loopWordRel loopLocalsRel retLookup dim
        retLabel loopVars gc noInstallCode wordCode frameDef frameSizeDef space inputCode anything cr c
        jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode
        pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
    refine ⟨bs,n,outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
    have ffiRel : panPost.ffi = sourcePost.ffi := postRel.2.2.2.2.2.2.2.1
    rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace⟩
    · exact Or.inl ⟨matching,trace.trans (congrArg HolFfiState.ioEvents ffiRel.symm)⟩
    · exact Or.inr ⟨resource,(congrArg HolFfiState.ioEvents ffiRel) ▸ trace⟩
  · right
    have nameMember : name ∈ programs.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
    have notRaise : name ≠ raiseStubLocation := by intro h; subst name; exact noRaise nameMember
    have notStore : name ≠ storeConstsStubLocation := by intro h; subst name; exact noStore nameMember
    have loopShape : LoopSequenceSource loopProg := by
      rw [compiledCrep,pWhile,branchConditionWhileBranch_simp_fixed init initEq condition direct body tail bodyEq tailEq]
      exact LoopLiveSteps.optimise_sequence
        (branchConditionWhileBranch_wordSimpShape init initEq condition direct body tail bodyEq tailEq crepCtxt live)
    have wordShape := loopSequenceSource_word loopShape ctxt labels
    have inputs := wholeWordStack_entryColour_simulation_inputs wc ac programs name 1
      (LoopToWord.compHOL ctxt loopProg labels).1 member nodup notRaise notStore wordShape
    rw [← kDef, ← selected] at inputs
    obtain ⟨bs,n,bsPost,nPost,compiled,actualFrame,actualSize,_,_,_,_,actualFrameDef,actualSizeDef,
      compilation,_,found,_,_,_⟩ := inputs
    have actualFrameEq : actualFrame = frame := actualFrameDef.trans frameDef.symm
    rw [actualFrameEq] at actualSizeDef compilation
    have actualSizeEq : actualSize = frameSize := actualSizeDef.trans frameSizeDef.symm
    rw [actualSizeEq] at compilation
    rw [← codeEq] at found
    have kBound : 1 ≤ k := by rw [kDef]; have h := ok.1; omega
    have argSpace : 1-k = 0 := by omega
    have foundBody : sptLookup name entry.code = some (.seq (.stackAlloc frameSize) compiled) := by
      simp only [Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative, ← frameDef, ← frameSizeDef, compilation] at found
      simpa only [argSpace,Nat.sub_zero] using found
    obtain ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,events⟩ :=
      allocationFailureRiscVWithin entry name (sizeOf q * (6*(sizeOf loopProg * (2 * (crepFactor*(panFactor*limit+1)) + 1))+1)) frameSize compiled
        foundBody ok.2.2.2.1 (by omega) inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput
        oracle renamed lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
    have panSourceFfi : pan.ffi = source.ffi := panStateRel.2.2.2.2.2.2.2.1
    have sourceLoopFfi : source.ffi = loop.ffi := sourceRel.2.2.2.2.1
    have wordLoopFfi : word.ffi = loop.ffi := by obtain ⟨_,_,_,_,_,_,h,_,_,_,_,_⟩ := loopWordRel; exact h
    have wordEntryFfi : word.ffi = entry.ffi := by rw [wordDef]; rfl
    have initialFfi : entry.ffi = pan.ffi := wordEntryFfi.symm.trans (wordLoopFfi.trans (sourceLoopFfi.symm.trans panSourceFfi.symm))
    have eventPrefix := Flapjack.evaluateHOLFiniteState_ioEvents_mono
      (.seq panInit (.seq (.while panCondition panBody) panTail)) pan panResult panPost panRun
    refine ⟨ticks,finalMachine,finalFfi,tickBound,machineRun,?_⟩
    simpa only [events, initialFfi] using eventPrefix

end SteppedFlapjack.PanToCrepSteps
