import SteppedFlapjack.PanToCrepSteps.ConcreteDeclProgram
import SteppedFlapjack.PanToCrepSteps.GlobalDecl
import SteppedFlapjack.PanToCrepSteps.GlobalInitializers

/-! Original Pancake loop visits through the actual global entry to RISC-V. -/
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


/-- The concrete source executes in 13 counted steps, and its compiled RISC-V
execution is bounded under the stated initial-state and backend conditions. -/
theorem concreteDecl_riscvWithin {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (source : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (crepRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (entryName : MlString) (entryBody : CrepProgHOL 64)
    (ctxtEq : ctxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0)
    (sourceCodeEq : source.code = alistToFmapCodeExact crepPrograms)
    (loopCodeEq : target.code = sptFromAList (compileProgHOLExact arch crepPrograms))
    (wordCodeEq : word.code = sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)))
    (wordData : LoopWordDataRel target word)
    (localName : VarName) (returned : BitVec 64)
    (panInitializer : ExpHOL 64)
    (panInit panCalleeInit : ProgHOL 64) (panCondition : ExpHOL 64) (panBody panTail : ProgHOL 64)
    (callerContext : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState F))
    (originalState : PanSemStateFiniteExact 64 F) [DecidablePred originalState.memaddrs]
    (execRel : PanSemStateRelExec production originalState.toExact)
    (execRanged : PanSemStateRelExecRanged production)
    (nameRanged : NameRanged localName) (sourceClock : originalState.clock ≠ 0)
    (execContext : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) F)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (pan panMiddle : PanSemStateFiniteExact 64 F)
    (panReturnShape : ShapeHOL)
    (panInitRun : pan.evaluateHOLFiniteState panInit = (none,panMiddle))
    (panClock : panMiddle.clock ≠ 0)
    (initLocalised : localisedProgHOL panInit = true)
    (initialPanRel : panToCrepStateRelFiniteExact pan source)
    (initialExcpRel : panToCrepExcpRelFiniteExact callerContext.eids pan.eshapes)
    (initialLocalsRel : panToCrepLocalsRelFiniteExact callerContext pan.locals source.locals)
    (startName : MlString) (initializers : List (ProgHOL 64))
    (funs exns : List (DeclHOL 64)) (globalContext : PanGlobalsContextExact 64)
    (originalFound : originalState.code.lookup (newMainNameHOL (concreteDeclProgram startName localName returned)) =
      some ([],.dec (ofString localName) .one (.const 1) (.seq (.skip) (.seq (.while (.var .local (ofString localName)) (.assign .local (ofString localName) (.const 0))) (.return (.const returned)))),panReturnShape))
    (globalRel : panGlobalsStateRelHOLExact true globalContext originalState
      (callEntryStateHOLFinite panMiddle HolFiniteMapExact.empty))
    (initializerDef : panInitializer = compileExpExactHOL globalContext (.const 1))
    (calleeInitDef : panCalleeInit = compileProgExactHOL globalContext (.skip))
    (conditionDef : panCondition = compileExpExactHOL globalContext (.var .local (ofString localName)))
    (calleeBodyDef : panBody = compileProgExactHOL globalContext (.assign .local (ofString localName) (.const 0)))
    (calleeTailDef : panTail = compileProgExactHOL globalContext (.return (.const returned)))
    (globalCompiled :
      let renamed := fpermDecsHOL startName (newMainNameHOL (concreteDeclProgram startName localName returned)) (resortDeclsHOL (concreteDeclProgram startName localName returned))
      let initial : PanGlobalsContextExact 64 :=
        { globals := HolFiniteMapExact.empty, globalsSize := 0,
          maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
      compileDecsExactHOL initial renamed = (initializers,funs,exns,globalContext))
    (programsDef : crepPrograms = compileProgDeclsHOLW (compileTopExactHOL (concreteDeclProgram startName localName returned) startName))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (concreteDeclProgram startName localName returned) startName)).reverse)
    (callerDef : callerContext = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (concreteDeclProgram startName localName returned) startName))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL (concreteDeclProgram startName localName returned) startName)))
    (initDef : panInit = nestedSeqHOL initializers) (nameDef : name = newMainNameHOL (concreteDeclProgram startName localName returned))
    (entryNameDef : entryName = startName)
    (entryBodyDef : entryBody = .seq (compileProgExactHOLW callerContext panInit) (.call none name []))
    (liveDef : live = .ln) :
    ∃ countedResult originalFinal,
      evalPanValueFfiProgSteps execContext primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+7)
        production.locals production.globals production.memory production.ffi
        (.dec localName .one (.const 1) (.seq .skip (.seq (.while (.var .local localName)
          (.assign .local localName (.const 0))) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (countedResult,13) ∧
    let limit := sizeOf (nestedSeqHOL initializers) +
      (4 + sizeOf (compileProgExactHOL globalContext (.skip)) +
        sizeOf (compileProgExactHOL globalContext (.assign .local (ofString localName) (.const 0))) + sizeOf (compileProgExactHOL globalContext (.return (.const returned)))) *
        13 + 2
    ∃ panPost, panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globalContext originalFinal panPost ∧
    TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) ∧
    ∃ (value condition : CrepExpHOL 64),
    compileExpExactHOLW (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) panInitializer = ([value],.one) ∧
    compileExpExactHOLW (scalarDeclContext (ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []) (ofString localName)) panCondition = ([condition],.one) ∧
    let panContext := ctxtFcExactHOL callerContext.funcs callerContext.eids [] [] []
    let init := compileProgExactHOLW callerContext panInit
    let inner := scalarDeclContext panContext (ofString localName)
    let calleeInit := compileProgExactHOLW inner panCalleeInit
    let body := compileProgExactHOLW inner panBody
    let tail := compileProgExactHOLW inner panTail
    let loopEntry := optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))
    let loopLimit := branchTailDeclLoopLimit ctxt live name init (panContext.vmax+1) value calleeInit condition body tail
      (sizeOf init + 2 + (4 + sizeOf (compileProgExactHOLW inner panCalleeInit) +
        sizeOf (compileProgExactHOLW inner panBody) + sizeOf (compileProgExactHOLW inner panTail)) * limit)
    ∃ (post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64)),
    panToCrepStateRelFiniteExact panPost post ∧
    pcCompileCorrectResultRel panContext panPost post (some (.returned (.val (.word returned)))) result ∧
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
        ((LoopMachineOutcome (resultToLoop result) outcome ∧ finalFfi.ioEvents = originalFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧ finalFfi.ioEvents <+: originalFinal.ffi.ioEvents ∧
            targetPost.stackMax.getD (targetPost.stackLimit+1) > targetPost.stackLimit)) := by
  obtain ⟨countedResult,countedFinal,countedExec,countedRun,sourceBound,initializerShape,initShape,conditionShape,bodyShape,tailShape,_,_⟩ :=
    concreteDecl_source_inputs production originalState execRel execRanged localName nameRanged sourceClock returned
      callerContext startName execContext primitive handler functions fuel
  refine ⟨countedResult,countedFinal,countedExec,?_⟩
  have sourceBound' : controlSteps (.dec (ofString localName) .one (.const 1)
      (.seq .skip (.seq (.while (.var .local (ofString localName)) (.assign .local (ofString localName) (.const 0)))
        (.return (.const returned))))) originalState ≤ 13 := by
    simpa only [concreteDeclBody] using sourceBound
  have initSupported : BranchProgram callerContext panInit ∨ ∀ shape globalName value,
      DeclHOL.decl shape globalName value ∈
        fpermDecsHOL startName (newMainNameHOL (concreteDeclProgram startName localName returned))
          (resortDeclsHOL (concreteDeclProgram startName localName returned)) →
      ScalarExpression callerContext value := by
    right
    intro shape globalName value member
    exact (concreteDecl_no_globals startName localName returned shape globalName value member).elim
  have unique : (crepPrograms.map Prod.fst).Nodup := by
    rw [programsDef]
    exact concreteDecl_compiled_names_unique startName localName returned
  have globalFound := concreteDeclProgram_lookup startName localName returned
  have notInline := concreteDecl_notInline startName localName returned
  have localised := concreteDecl_localised startName localName returned
  have preShapes := concreteDecl_preInline_shapes startName localName returned
  have noTail : ∀ n ps init callee,
      (n,ps,.seq init (.call none callee [])) ∈ compileToCrepExactHOLW
        (compileTopExactHOL (concreteDeclProgram startName localName returned) startName) →
      callee ∉ (functionsHOL ((compileTopExactHOL (concreteDeclProgram startName localName returned) startName).filter inlinableHOL)).map Prod.fst := by
    intro n ps init callee _
    rw [concreteDecl_inline_selection_empty]
    simp
  exact panOriginalDeclEntry_riscvWithin ctxt live name source target word crepRel memRel globalsRel localsRel
    arch crepPrograms entryName entryBody unique ctxtEq sourceCodeEq loopCodeEq wordCodeEq wordData
    (ofString localName) panInitializer panInit panCalleeInit panCondition panBody panTail callerContext
    (.const 1) .skip (.var .local (ofString localName)) (.assign .local (ofString localName) (.const 0))
    (.return (.const returned)) originalState countedFinal 13 sourceBound' initializerShape initShape conditionShape bodyShape tailShape
    pan panMiddle (some (.returned (.val (.word returned)))) panReturnShape panInitRun panClock (.return _) initLocalised initialPanRel initialExcpRel initialLocalsRel
    (concreteDeclProgram startName localName returned) startName initializers .one (by simpa only [concreteDeclBody] using globalFound) funs exns globalContext
    (by simpa only [concreteDeclBody] using countedRun) originalFound globalRel
    initializerDef calleeInitDef conditionDef calleeBodyDef calleeTailDef globalCompiled initSupported notInline programsDef
    panCode localised preShapes noTail callerDef initDef nameDef entryNameDef entryBodyDef liveDef

end SteppedFlapjack.PanToCrepSteps
