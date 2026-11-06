import SteppedFlapjack.PanToCrepSteps.ConcreteDeclFrame
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclNativeRiscV

/-! Counted source execution with selected native frame and RISC-V execution. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemControl Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.LabToTargetSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.StackToLabSteps SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs.InitializationStateRel Flapjack.WordSemStateFiniteExact
open Flapjack.PanSemStateFiniteExact




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




/-- The selected concrete frame supplies the counted RISC-V execution bound. -/
theorem concreteDecl_counted_riscv_with_frame {F : Type}
    (arch : AsmArchitecture) (start : MlString) (name : VarName) (returned : BitVec 64)
    (pan : PanSemStateFiniteExact 64 F)
    (originalState : PanSemStateFiniteExact 64 F) [DecidablePred originalState.memaddrs] [DecidablePred originalState.shMemaddrs]
    (originalDef : originalState = concreteDeclOriginalState start name returned
      (callEntryStateHOLFinite pan HolFiniteMapExact.empty))
    (ffiState : FfiState F) (ffiRel : FfiStateRel ffiState originalState.ffi)
    (nameRanged : NameRanged name) (sourceClock : originalState.clock ≠ 0)
    (execContext : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) F)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (state : CrepSemHOLState 64 F)
    (stateDef : state = concreteDeclCrepState pan (compileProgDeclsHOLW
      (compileTopExactHOL (concreteDeclProgram start name returned) start)))
    (panClock : pan.clock ≠ 0) (panLocalsEmpty : pan.locals = HolFiniteMapExact.empty)
    (panExceptionsEmpty : pan.eshapes = HolFiniteMapExact.empty)
    (panGlobalsEmpty : pan.globals = HolFiniteMapExact.empty)
    (panStructs : pan.structs = []) (panTopOutside : ¬ pan.memaddrs pan.topAddr)
    (panAligned : panGlobalsByteAlignedHOL pan.topAddr)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse)
    (wc : Compiler.Backend.WordToWord.Config) (ac : Compiler.Encoders.Asm.AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL (concreteDeclProgram start name returned) start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL
        (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL (concreteDeclProgram start name returned) start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit initialClock : Nat)
    (heapLength : BitVec 64)
    (memory : stack.memory = (concreteDeclLoopState arch state (compileProgDeclsHOLW
      (compileTopExactHOL (concreteDeclProgram start name returned) start))).memory)
    (domain : stack.mdomain = (concreteDeclLoopState arch state (compileProgDeclsHOLW
      (compileTopExactHOL (concreteDeclProgram start name returned) start))).mdomain)
    (shared : stack.shMdomain = (concreteDeclLoopState arch state (compileProgDeclsHOLW
      (compileTopExactHOL (concreteDeclProgram start name returned) start))).shMdomain)
    (clock : stack.clock = state.clock) (endian : stack.be = state.be) (ffi : stack.ffi = state.ffi)
    (current : stack.store.lookup .currHeap = some (.word state.baseAddr))
    (length : stack.store.lookup .heapLength = some (.word heapLength))
    (heap : state.topAddr = state.baseAddr + 2 * heapLength)
    (inputCode : List (Nat × HolProg 64))
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (f : Spt Nat) (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F) (lab : LabSem.State 64 LabToTarget.Config F)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (distinct : (inputCode.map Prod.fst).Nodup) (sourceCode : stack.code = sptFromAList inputCode)
    (pre : Pre cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := initialClock} stack.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := initialClock} 0 stack.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (rel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc firstLoopName 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    let production := panSemExecStateOfHOLWithKeys originalState ffiState
      [newMainNameHOL (concreteDeclProgram start name returned)]
    ∃ countedResult originalFinal,
      evalPanValueFfiProgSteps execContext primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+7)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const 1) (.seq .skip (.seq (.while (.var .local name)
          (.assign .local name (.const 0))) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (countedResult,13) ∧
      originalState.evaluateHOLFiniteState (concreteDeclBody name returned) =
        (some (.returned (.val (.word returned))),originalFinal) ∧
      controlSteps (concreteDeclBody name returned) originalState ≤ 13 ∧
    let lowered := compileTopExactHOL (concreteDeclProgram start name returned) start
    let sourceContext : PanToCrepContextExact 64 := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW sourceContext (nestedSeqHOL ([] : List (ProgHOL 64)))
    let code := compileProgDeclsHOLW lowered
    let loopContext := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable code) 0
    let loop := optimiseHOL (compileHOLExact loopContext .ln (.seq init (.call none (newMainNameHOL (concreteDeclProgram start name returned)) [])))
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL loop .ln) (toNumSetHOL []))) .ln
    let programs := loopToWordCompileHOL (compileProgHOLExact arch code)
    let q := (LoopToWord.compHOL ctxt loop (firstLoopName,2)).1
    let out := (Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,q),SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName)).2.2
    ∃ bs n bsPost nPost body frame frameSize,
      SteppedFlapjack.WordToStackSteps.nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length))
        firstLoopName (Compiler.Backend.WordToWord.compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL out / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (1-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      Compiler.Backend.WordToStack.Native.compNative ac false out (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup firstLoopName stack.code = some (Compiler.Backend.WordToStack.Native.compileProgNative ac false out 1 (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ stack.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (stack.bitmaps.drop (n-(appListAppend bs).length)) ∧
      maxVarHOL out < 2*frame+2*(ac.regCount-(5+ac.avoidRegs.length)) ∧
      (∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact stack.code loc) ∧
      (frameSize ≤ stack.stackSpace ∧
       (let sourceWord := {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
         (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
           stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle) with
             code := sptFromAList programs}
        CrepToLoopSteps.LoopWordDataRel (concreteDeclLoopState arch state code) sourceWord ∧
        concreteDeclWordState arch state code sourceWord heapLength = sourceWord) ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        (WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle))
        {stack with stackSpace := stack.stackSpace-frameSize} [] 0 ∧
       Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
        {(WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
          (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle)) with clock := limit}
        {stack with stackSpace := stack.stackSpace-frameSize,clock := limit} [] 0 ∧
       (∀ temp replayClock,
         let sourceWord := {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
           (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
             stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle) with
               code := sptFromAList programs}
         (∀ loopState : LoopSemStateFiniteExact 64 F,
           CrepToLoopSteps.LoopWordDataRel loopState sourceWord ↔
           CrepToLoopSteps.LoopWordDataRel loopState
             {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
               (Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length))
                 stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2) coracle) with
                   code := sptFromAList programs}) ∧
         Flapjack.Compiler.Backend.WordSimp.gcFunConstOk sourceWord.gcFun ∧
         sptDomain sourceWord.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
         wordLocalsRel temp sourceWord.locals sourceWord.locals ∧
         sptLookup 0 sourceWord.locals = some (.loc 1 0) ∧
         Flapjack.WordToStackProofs.stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize frame
           {sourceWord with code := (sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2), locals := sourceWord.locals, clock := replayClock}
           {stack with stackSpace := stack.stackSpace-frameSize,clock := replayClock} [] 0 ∧
         LoopToWord.localsRelHOL ctxt .ln sourceWord.locals ∧
         ∀ k, sptMem k (accVarsHOL loop .ln) → sptMem k ctxt) ∧
       (∃ (value condition : CrepExpHOL 64),
        compileExpExactHOLW (ctxtFcExactHOL sourceContext.funcs sourceContext.eids [] [] []) (.const 1) = ([value],.one) ∧
        compileExpExactHOLW (scalarDeclContext (ctxtFcExactHOL sourceContext.funcs sourceContext.eids [] [] []) (ofString name)) (.var .local (ofString name)) = ([condition],.one) ∧
        let panContext := ctxtFcExactHOL sourceContext.funcs sourceContext.eids [] [] []
        let inner := scalarDeclContext panContext (ofString name)
        let calleeInit := compileProgExactHOLW inner (.skip)
        let bodyCrep := compileProgExactHOLW inner (.assign .local (ofString name) (.const 0))
        let tail := compileProgExactHOLW inner (.return (.const returned))
        let sourceLimit := sizeOf (nestedSeqHOL ([] : List (ProgHOL 64))) +
          (4 + sizeOf (compileProgExactHOL (concreteDeclGlobalContext start name returned) (.skip)) +
            sizeOf (compileProgExactHOL (concreteDeclGlobalContext start name returned) (.assign .local (ofString name) (.const 0))) +
            sizeOf (compileProgExactHOL (concreteDeclGlobalContext start name returned) (.return (.const returned)))) * 13 + 2
        let loopLimit := branchTailDeclLoopLimit loopContext .ln (newMainNameHOL (concreteDeclProgram start name returned)) init
          (panContext.vmax+1) value calleeInit condition bodyCrep tail
          (sizeOf init + 2 + (4 + sizeOf (compileProgExactHOLW inner (.skip)) +
            sizeOf (compileProgExactHOLW inner (.assign .local (ofString name) (.const 0))) +
            sizeOf (compileProgExactHOLW inner (.return (.const returned)))) * sourceLimit)
        let compiledCode := sptFromAList (Compiler.Backend.WordToWord.compile wc ac programs).2
        let stackLimit := tailStackReplayLimit ac 1 firstLoopName wc.regAlg (ac.regCount-(5+ac.avoidRegs.length))
          (SteppedFlapjack.WordAllocSteps.entryColour wc programs firstLoopName) loop ctxt (firstLoopName,2) compiledCode loopLimit
        ∃ (outcome : HolOutcome) (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
          ticks ≤ labTickBound 4 labCode lab.codeBuffer *
            (flattenStepFactor * (computedRunCost bounds
              (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit stack.code out (bs,n)
                (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame)))
              (.call none (.inl firstLoopName) none)
              (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackLimit+1} 0 stack.regs) *
              (uniformFactor (width := 64) c * (3 + callSequenceCost ac stackLimit stack.code out (bs,n)
                (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame))) + 4)) ∧
          evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome,finalMachine,finalFfi)) ∨
       ∃ (ticks : Nat) (finalMachine : RiscV.L3.riscv_state) (finalFfi : HolFfiState F),
         ticks ≤ labTickBound 4 labCode lab.codeBuffer *
          (flattenStepFactor * (computedRunCost bounds (uniformFactor (width := 64) c * 3)
            (.call none (.inl firstLoopName) none)
            (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode), clock := limit+1} 0 stack.regs) *
            (uniformFactor (width := 64) c * 3) + 4)) ∧
         evaluateTargetHOL mc lab.ffi ticks machine = (.halt HolOutcome.resourceLimitHit,finalMachine,finalFfi) ∧
         finalFfi.ioEvents = stack.ffi.ioEvents ∧ finalFfi.ioEvents = originalState.ffi.ioEvents) := by
  obtain ⟨countedResult,originalFinal,sourceExec,sourceRun,sourceBound,bs,n,bsPost,nPost,body,frame,frameSize,
    selected,frameDef,sizeDef,compilation,foundEntry,lengthBound,gapBound,bitmapPrefix,maxBound,labelCheck,alternatives⟩ :=
    concreteDecl_counted_frame_or_riscvResource arch start name returned pan originalState originalDef ffiState ffiRel
      nameRanged sourceClock execContext primitive handler functions fuel state stateDef wc ac stack coracle codeEq
      bitmapsPrefix ok limit initialClock heapLength memory domain shared clock endian ffi current length heap
      inputCode anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode
      labs asm machine distinct sourceCode pre relation ha hs hk hf hcode hor rel hpc hmc tie machineRel
  refine ⟨countedResult,originalFinal,sourceExec,sourceRun,sourceBound,bs,n,bsPost,nPost,body,frame,frameSize,
    selected,frameDef,sizeDef,compilation,foundEntry,lengthBound,gapBound,bitmapPrefix,maxBound,labelCheck,?_⟩
  rcases alternatives with ⟨space,data,initial,clocked,remaining⟩ | resource
  · left
    refine ⟨space,data,initial,clocked,remaining,?_⟩
    let programs := compileProgDeclsHOLW (compileTopExactHOL (concreteDeclProgram start name returned) start)
    let caller := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)))
      (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start))
    let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0
    let word := {WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
        (sptFromAList (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch programs))).2) coracle) with
          code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs))}
    obtain ⟨_,_,_,panPost,panRel,shapes,value,condition,valueEq,conditionEq,post,result,postRel,resultRel,extra,loopPost,loopRel,backend⟩ :=
      concreteDecl_native_riscvWithin ctxt .ln (newMainNameHOL (concreteDeclProgram start name returned)) state
        (concreteDeclLoopState arch state programs) word arch programs start
        (.seq (compileProgExactHOLW caller (.skip : ProgHOL 64)) (.call none (newMainNameHOL (concreteDeclProgram start name returned)) []))
        rfl name returned caller start originalState ffiState ffiRel nameRanged sourceClock execContext primitive handler functions fuel
        pan panClock originalDef panLocalsEmpty panExceptionsEmpty stateDef rfl ac (ac.regCount-(5+ac.avoidRegs.length)) frameSize
        stack (sptFromAList (Compiler.Backend.WordToWord.compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch programs))).2)
        coracle heapLength memory domain shared clock endian ffi current length rfl heap panGlobalsEmpty panStructs panTopOutside
        panAligned rfl panCode rfl rfl rfl rfl rfl
    have space' : frameSize - (1-(ac.regCount-(5+ac.avoidRegs.length))) ≤ stack.stackSpace := by omega
    obtain ⟨_,outcome,ticks,finalMachine,finalFfi,_,_,bound,run,_⟩ :=
      backend ac wc stack frameSize frame coracle rfl ok initial bs bsPost n nPost body compilation lengthBound
        gapBound bitmapPrefix labelCheck maxBound frameDef sizeDef space' foundEntry inputCode anything cr c jump bounds pointer
        f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine initialClock distinct sourceCode pre relation
        ha hs hk hf hcode hor rel hpc hmc tie machineRel
    exact ⟨value,condition,valueEq,conditionEq,outcome,ticks,finalMachine,finalFfi,bound,run⟩
  · exact Or.inr resource

end SteppedFlapjack.PanToCrepSteps
