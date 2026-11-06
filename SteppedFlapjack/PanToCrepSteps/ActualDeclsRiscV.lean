import SteppedFlapjack.PanToCrepSteps.ActualWordRiscV
import SteppedFlapjack.CrepToLoopSteps.InlineFixed
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
theorem panBranchConditionWhileBranch_actualDecls_allFrames_riscvWithin {F : Type}
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
    (arch : AsmArchitecture)
    (crepCode : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64))
    (declarations : List (DeclHOL 64)) (index : Nat)
    (functionBound : index < (functionsHOL declarations).length) (sourceName : Basis.Pure.MlString.MlString)
    (returnShape : ShapeHOL)
    (functionEntry : (functionsHOL declarations)[index] =
      (sourceName,[],.seq panInit (.seq (.while panCondition panBody) panTail),returnShape))
    (crepCodeDef : crepCode = compileProgDeclsHOLW declarations)
    (panContextDef : panContext = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL declarations)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL declarations))
    (programsDef : programs = loopToWordCompileHOL (compileProgHOLExact arch crepCode))
    (nameDef : name = index + firstLoopName)
    (crepCtxtDef : crepCtxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepCode) (([] : List Nat).length-1))
    (liveDef : live = listToNumSetHOLExact (List.range ([] : List Nat).length))
    (ctxtDef : ctxt = makeCtxtHOL 2 (LoopToWord.fromNumSetHOL (sptDifference (accVarsHOL loopProg .ln) (LoopToWord.toNumSetHOL []))) .ln)
    (labelsDef : labels = (name,2))
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
  have initEq : CrepToLoopSteps.BranchProgram (compileProgExactHOLW panContext panInit) := branch_compile panInitShape
  have bodyEq : CrepToLoopSteps.BranchProgram (compileProgExactHOLW panContext panBody) := branch_compile panBodyShape
  have tailEq : CrepToLoopSteps.BranchProgram (compileProgExactHOLW panContext panTail) := branch_compile panTailShape
  obtain ⟨actualBound,actualEntry⟩ := compileProgDecls_pancake_entry declarations index functionBound sourceName
    panInit panCondition panBody panTail returnShape functionEntry panContext panContextDef initEq condition conditionDef bodyEq tailEq
  have indexBound : index < crepCode.length := by simpa only [crepCodeDef] using actualBound
  have sourceEntry : crepCode[index] = (sourceName,[],p) := by
    simpa only [crepCodeDef,pDef] using actualEntry
  exact panBranchConditionWhileBranch_actualWord_allFrames_riscvWithin wc ac programs name k panInit panCondition panBody panTail panContext
    panInitShape panShape panBodyShape panTailShape pan panPost panResult panComplete panRun panLocalised source
    panStateRel panCodeRel panExcpRel panLocalsRel init initDef condition conditionDef body bodyDef tail tailDef p pDef panFactor panFactorDef
    crepCtxt live loopProg compiledCrep crepFactor crepFactorDef loop word ctxt labels arch crepCode index indexBound sourceName sourceEntry
    programsDef nameDef crepCtxtDef liveDef ctxtDef labelsDef nodup noRaise noStore q kDef selected entry coracle codeEq bitmapsPrefix ok
    frameSize frame limit wordDef stepBound sourceRel memRel globalsRel codeRel localsRel loopWordRel loopLocalsRel retLookup dim retLabel
    gc noInstallCode wordCode frameDef frameSizeDef inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed
    lab pc mc labCode labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel

end SteppedFlapjack.PanToCrepSteps
