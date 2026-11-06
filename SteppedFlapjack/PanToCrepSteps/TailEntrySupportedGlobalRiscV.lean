import SteppedFlapjack.PanToCrepSteps.TailEntryGlobalWordRiscV
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! The global machine bound with frontend code facts derived from source compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect SteppedFlapjack.WordToStackSteps
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
open SteppedFlapjack.StackToLabSteps SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps


open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Specialize the global machine bound to supported post-inlining source code. -/
theorem panTailEntry_supportedGlobal_riscvWithin {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (source : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (limit : Nat)
    (crepRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (entryName : MlString) (entryBody : CrepProgHOL 64)
    (unique : (crepPrograms.map Prod.fst).Nodup)
    (ctxtEq : ctxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0)
    (sourceCodeEq : source.code = alistToFmapCodeExact crepPrograms)
    (loopCodeEq : target.code = sptFromAList (compileProgHOLExact arch crepPrograms))
    (wordCodeEq : word.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)))
    (wordData : LoopWordDataRel target word)
    (panInit panCalleeInit : ProgHOL 64) (panCondition : ExpHOL 64) (panBody panTail : ProgHOL 64)
    (callerContext : PanToCrepContextExact 64)
    (sourceInitShape : PanToCrepSteps.BranchProgram callerContext panInit)
    (panInitShape : PanToCrepSteps.BranchProgram (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panCalleeInit)
    (panConditionShape : ScalarExpression (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panCondition)
    (panBodyShape : PanToCrepSteps.BranchProgram (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panBody)
    (panTailShape : PanToCrepSteps.BranchProgram (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panTail)
    (pan panMiddle panPost : PanSemStateFiniteExact 64 F) (panResult : Option (PanSemResultExact 64))
    (panLocals : HolFiniteMapExact MlString (ValueHOL 64)) (panReturnShape : ShapeHOL)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panLookup : lookupCodeHOLFinite panMiddle.code.lookup name [] =
      some (.seq panCalleeInit (.seq (.while panCondition panBody) panTail),panLocals,panReturnShape))
    (panClock : panMiddle.clock ≠ 0)
    (panRun : (callEntryStateHOLFinite panMiddle panLocals).evaluateHOLFiniteState
      (.seq panCalleeInit (.seq (.while panCondition panBody) panTail)) = (panResult,panPost))
    (panComplete : CompletePanResult panResult)
    (initLocalised : localisedProgHOL panInit = true)
    (initialPanRel : panToCrepStateRelFiniteExact pan source)
    (initialExcpRel : panToCrepExcpRelFiniteExact callerContext.eids pan.eshapes)
    (initialLocalsRel : panToCrepLocalsRelFiniteExact callerContext pan.locals source.locals)
    (panBound : globalEntrySteps panInit name [] pan ≤ limit)
    (declarations : List (DeclHOL 64)) (startName : MlString) (initializers : List (ProgHOL 64))
    (returnShape : ShapeHOL) (original : ProgHOL 64)
    (globalFound : (functionsHOL declarations).lookup startName = some ([],original,returnShape))
    (funs exns : List (DeclHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (globalCompiled :
      let renamed := fpermDecsHOL startName (newMainNameHOL declarations) (resortDeclsHOL declarations)
      let initial : PanGlobalsContextExact 64 :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,globalContext))
    (notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations startName).filter inlinableHOL)).map Prod.fst)
    (programsDef : crepPrograms = compileProgDeclsHOLW (compileTopExactHOL declarations startName))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations startName)).reverse)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations startName), localisedProgHOL entry.2.2.1 = true)
    (preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations startName) → SupportedCodeBody p)
    (noTail : ∀ n ps init callee,
      (n,ps,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations startName) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations startName).filter inlinableHOL)).map Prod.fst)
    (callerDef : callerContext = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations startName))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations startName)))
    (initDef : panInit = nestedSeqHOL initializers) (nameDef : name = newMainNameHOL declarations)
    (entryNameDef : entryName = startName)
    (entryBodyDef : entryBody = .seq (compileProgExactHOLW callerContext panInit) (.call none name []))
    (liveDef : live = .ln) :
    TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) ∧
    ∃ (condition : CrepExpHOL 64),
    compileExpExactHOLW (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panCondition = ([condition],.one) ∧
    let panContext := ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []
    let init := compileProgExactHOLW callerContext panInit
    let calleeInit := compileProgExactHOLW panContext panCalleeInit
    let body := compileProgExactHOLW panContext panBody
    let tail := compileProgExactHOLW panContext panTail
    let loopEntry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let loopLimit := branchTailLoopLimit ctxt live name init calleeInit condition body tail
      (sizeOf init + 2 + (3 + sizeOf (compileProgExactHOLW panContext panCalleeInit) +
        sizeOf (compileProgExactHOLW panContext panBody) + sizeOf (compileProgExactHOLW panContext panTail)) * limit)
    ∃ (post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64)),
    panToCrepStateRelFiniteExact panPost post ∧
    pcCompileCorrectResultRel panContext panPost post panResult result ∧
    ∃ extra loopPost, crepToLoopStateRelExact post loopPost ∧
    let shiftedWord := {word with clock := word.clock+extra}
    let count := 1
    let entryName := firstLoopName
    let wordCtxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL loopEntry .ln) (LoopToWord.toNumSetHOL []))) .ln
    let labels := (firstLoopName,2)
    let programs := loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
    ∀ (ac : AsmConfigExact 64) (wc : Flapjack.Compiler.Backend.WordToWord.Config),
    let alg := wc.regAlg
    let regCount := ac.regCount-(5+ac.avoidRegs.length)
    let col := entryColour wc programs entryName
    let compiledCode := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2
    let wordBody := (LoopToWord.compHOL wordCtxt loopEntry labels).1
    let out := (fullCompileSingle ac.twoRegArith regCount alg ac ((entryName,count,wordBody),col)).2.2
    let locals := word.locals
    ∀ (entry : StackSemStateFiniteExact 64 LabToTarget.Config F) (frameSize frame : Nat)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (_wordInit : word = {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac regCount entry compiledCode coracle) with
        code := sptFromAList programs})
    (_initOk : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac regCount entry coracle)
    (_initialFrame : stateRel ac regCount frameSize frame
      (WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac regCount entry compiledCode coracle))
      {entry with stackSpace := entry.stackSpace-frameSize} [] 0)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64),
    let lens : List Nat := []
    let start := firstLoopName
    let argumentCount := 1
    ∀ (_native : Flapjack.Compiler.Backend.WordToStack.Native.compNative ac false
      out
      (bs,n) (regCount,frameSize,frame) = (compiled,(bsPost,nPost)))
    (_lengthBound : (appListAppend bs).length ≤ n) (_bitmapBound : n-(appListAppend bs).length ≤ entry.bitmaps.length)
    (_bitmapPrefix : List.IsPrefix (appListAppend bsPost) (entry.bitmaps.drop (n-(appListAppend bs).length)))
    (_labelCheck : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact entry.code loc)
    (_maxBound : maxVarHOL out < 2*frame+2*regCount)
    (_frameDef : frame = max (maxVarHOL out / 2 + 1 - regCount) (argumentCount-regCount))
    (_frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (_space : frameSize-(argumentCount-regCount) ≤ entry.stackSpace)
    (_found : sptLookup start entry.code = some (Flapjack.Compiler.Backend.WordToStack.Native.compileProgNative ac false
      out argumentCount regCount (bs,n)).1)
    (inputCode : List (Nat × HolProg 64)) (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat) (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat)
    (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state) (initialClock : Nat)
    (_distinct : (inputCode.map Prod.fst).Nodup) (_sourceCode : entry.code = sptFromAList inputCode)
    (_pre : Pre cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := initialClock} entry.regs)
    (_relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := initialClock} 0 entry.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (_ha : ¬renamed.useAlloc) (_hs : ¬renamed.useStore) (_hk : ¬renamed.useStack)
    (_hf : Function.Bijective (findNameSpt f))
    (_hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (_hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (_labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (_hpc : LabSem.locToPc start 0 lab.code = some lab.pc)
    (_hmc : mc.target = riscvTarget) (_tie : LabToTarget.oracleTie mc machine lab)
    (_machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine),
    let stackLimit := tailStackReplayLimit ac count entryName alg regCount col loopEntry wordCtxt labels compiledCode loopLimit
    sptLookup entryName compiledCode = some (count,out) ∧
    ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F)
      (stackPost : StackSemStateFiniteExact 64 LabToTarget.Config F) (stackResult : Option (StackSemResult 64)),
      ticks ≤ labTickBound 4 labCode lab.codeBuffer *
        (flattenStepFactor * (computedRunCost bounds
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame)))
          (.call none (.inl start) none)
          (Tgt anything cr c {entry with code := sptFromAList (StackRawCall.compile inputCode),clock := stackLimit+1} 0 entry.regs) *
          (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit entry.code out (bs,n) (regCount,frameSize,frame))) + 4)) ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = stackPost.ffi.ioEvents ∧ stackEntryClass stackResult = .CompleteResult outcome ∧
      ∃ wordPost wordResult perm selectedLocals targetPost,
        LoopToWord.CompileCorrect.resultCase wordCtxt (.loc 1 0) shiftedWord (resultToLoop result) loopPost wordResult wordPost ∧
        wordPost.ffi = loopPost.ffi ∧
        wordStateEqRel {wordPost with code := compiledCode,permute := perm,locals := selectedLocals,clock := tailWordReplayLimit loopEntry wordCtxt labels compiledCode loopLimit-(6*loopLimit-(6*loopLimit-(shiftedWord.clock-wordPost.clock)))} targetPost ∧
        compCorrectResult ac regCount frameSize frame
          {shiftedWord with code := compiledCode,locals := locals,clock := stackLimit}
          {targetPost with clock := stackLimit-(tailWordReplayLimit loopEntry wordCtxt labels compiledCode loopLimit-targetPost.clock)}
          stackPost wordResult stackResult lens ∧
        ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = panPost.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: panPost.ffi.ioEvents ∧
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) := by
  have actualCode : source.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations startName)) := by
    simpa only [programsDef] using sourceCodeEq
  have actualUnique : ((compileProgDeclsHOLW (compileTopExactHOL declarations startName)).map Prod.fst).Nodup := by
    simpa only [programsDef] using unique
  obtain ⟨codeRel,shapes⟩ := global_supported_panCrep_codeAndShapes declarations startName pan source
    panCode actualCode actualUnique localised preShapes noTail
  have programShapes : ∀ n ps p, (n,ps,p) ∈ crepPrograms → SupportedCodeBody p := by
    simpa only [programsDef] using shapes
  have initialCodeRel : codeRelExactHOLW callerContext pan.code source.code := by
    rw [callerDef]
    exact codeRel
  exact panTailEntry_globalWord_riscvWithin ctxt live name source target word limit crepRel memRel globalsRel localsRel
    arch crepPrograms entryName entryBody unique programShapes ctxtEq sourceCodeEq loopCodeEq wordCodeEq wordData
    panInit panCalleeInit panCondition panBody panTail callerContext sourceInitShape panInitShape panConditionShape panBodyShape
    panTailShape pan panMiddle panPost panResult panLocals panReturnShape panInitRun panLookup panClock panRun panComplete
    initLocalised initialPanRel initialCodeRel initialExcpRel initialLocalsRel panBound declarations startName initializers
    returnShape original globalFound funs exns globalContext globalCompiled notInline programsDef callerDef initDef nameDef
    entryNameDef entryBodyDef liveDef

end SteppedFlapjack.PanToCrepSteps
