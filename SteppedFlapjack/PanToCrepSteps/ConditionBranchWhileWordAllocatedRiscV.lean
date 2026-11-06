import SteppedFlapjack.PanToCrepSteps.ConditionBranchWhile
import SteppedFlapjack.PanToCrepSteps.WhileRiscV
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefixWordAllocatedRiscV
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

/-- A completed Pancake initialization, loop and continuation bounds the RISC-V run through the complete Word compiler, with outcome and trace correspondence or a resource-limit prefix. -/
theorem panBranchConditionWhileBranch_wordAllocated_riscvWithin {F : Type}
    (ac : AsmConfigExact 64) (count name alg k : Nat) (col : Option (Spt Nat))
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
    (loopProg : HolLoopProg 64) (compiledCrep : loopProg = compileHOLExact crepCtxt live p)
    (crepFactor : Nat) (crepFactorDef : crepFactor =
      1 + sizeOf (compileHOLExact crepCtxt live init) +
        (1 + (1 + sizeOf (compileHOLExact crepCtxt live (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact crepCtxt (crepCtxt.vmax+1) live condition).1) +
            sizeOf (compileHOLExact crepCtxt live body)+3) + sizeOf (compileHOLExact crepCtxt live tail)))
    (loop : LoopSemStateFiniteExact 64 F)
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (locals : Spt (WordLocW 64))
    (q : WordLangProgHOL (BitVec 64))
    (selected : q = (fullCompileSingle ac.twoRegArith k alg ac ((name,count,(LoopToWord.compHOL ctxt loopProg labels).1),col)).2.2)
    (entry : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (frameSize frame limit : Nat) (lens : List Nat) (bs bsPost : AppList (BitVec 64)) (n nPost : Nat)
    (compiled : HolProg 64) (start argumentCount : Nat)
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
    (localRel : wordLocalsRel (maxVarHOL (compileExp (LoopToWord.compHOL ctxt loopProg labels).1)+1) word.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count))
    (noInstallCode : WordProps.noInstallCode word.code)
    (wordCode : ∀ loc arity r, sptLookup loc word.code = some (arity,r) → LoopBlock r)
    (wordPremises : stateRel ac k frameSize frame {word with locals := locals}
      {entry with stackSpace := entry.stackSpace - (frameSize - (argumentCount-k))} lens 0 ∧
      Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false q (bs,n) (k,frameSize,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ entry.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc))
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
    (pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(crepFactor*(panFactor*limit+1))+1))+1} entry.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(crepFactor*(panFactor*limit+1))+1))+1} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    ∃ (result : Option (CrepResultHOLExact 64)) (sourcePost : CrepSemHOLState 64 F)
      (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state)
      (finalFfi : HolFfiState F),
      pcCompileCorrectResultRel panContext panPost sourcePost panResult result ∧
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(crepFactor*(panFactor*limit+1))+1)) entry.code q (bs,n) (k,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode), clock := (sizeOf q * (6*(crepFactor*(panFactor*limit+1))+1))+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac (sizeOf q * (6*(crepFactor*(panFactor*limit+1))+1)) entry.code q (bs,n) (k,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = panPost.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: panPost.ffi.ioEvents)) := by
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
  obtain ⟨outcome,ticks,finalMachine,finalFfi,tickBound,machineRun,correspondence⟩ :=
    branchConditionWhileBranch_wordAllocated_riscvWithin ac count name alg k col init initEq condition direct body tail bodyEq tailEq p pWhile source sourcePost result
      crepCtxt live loopProg compiledCrep crepFactor crepFactorDef loop word ctxt labels locals q selected
      entry frameSize frame (panFactor*limit) lens bs bsPost n nPost compiled start argumentCount complete crepLimit
      (by simpa [pDef] using sourceRun) sourceRel memRel globalsRel codeRel localsRel loopWordRel loopLocalsRel retLookup dim
      retLabel loopVars gc localRel domain noInstallCode wordCode wordPremises frameDef frameSizeDef space found inputCode anything cr c
      jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine distinct sourceCode
      pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  refine ⟨result,sourcePost,outcome,ticks,finalMachine,finalFfi,resultRel,tickBound,machineRun,?_⟩
  have ffiRel : panPost.ffi = sourcePost.ffi := postRel.2.2.2.2.2.2.2.1
  rcases correspondence with ⟨matching,trace⟩ | ⟨resource,trace⟩
  · exact Or.inl ⟨matching,trace.trans (congrArg HolFfiState.ioEvents ffiRel.symm)⟩
  · exact Or.inr ⟨resource,(congrArg HolFfiState.ioEvents ffiRel) ▸ trace⟩

end SteppedFlapjack.PanToCrepSteps
