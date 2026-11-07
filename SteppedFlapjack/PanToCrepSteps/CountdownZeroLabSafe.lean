import SteppedFlapjack.PanToCrepSteps.CountdownZeroCountedSafe
import SteppedFlapjack.PanToCrepSteps.LabCountedFullCompiler

/-! Successful zero-count execution from the Lab initializer. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- The Lab-initialized source run has a successful bounded machine run. -/
theorem countdownZero_labInitialized_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (arch : AsmArchitecture) (name : VarName) (initial returned : BitVec 64)
    (condition assignment : Exp (RiscV.Word 64)) (cost budget : Nat)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack)
    (cfg : LabToTarget.Config)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production) (ffiRel : FfiStateRel production.ffi backend.lab.ffi)
    (nameRanged : NameRanged name) (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (sourceClock : cost ≤ (backend.lab.clock-1)*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) + 7) (clockPositive : 0 < backend.lab.clock)
    (budgetBound : cost ≤ budget)
    (returnLocals returnGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnMemory : BitVec 64 → Option (PanValue (BitVec 64))) (returnFfi : FfiState σ)
    (returnValues : List (PanValue (RiscV.Word 64)))
    (wholeRun : let prod := labInitializedProduction production template stack backend
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+4)
        prod.locals prod.globals prod.memory prod.ffi
        (.dec name .one (.const initial) (.seq .skip (.seq
          (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) =
          some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost))
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (templateLocals : template.locals = HolFiniteMapExact.empty)
    (templateGlobals : template.globals = HolFiniteMapExact.empty)
    (templateExceptions : template.eshapes = HolFiniteMapExact.empty)
    (templateStructs : template.structs = [])
    (startDef : start = ofString "main")
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const initial)
      (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))
    (sourceCode : template.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const initial)
        (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))),.one)))
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const initial)
        (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))))).2)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], []))
    (wordMemory : ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word)
    (acEq : ac = riscvConfig) (archEq : arch = riscvConfig.isa)
    (wcEq : wc = countdownRiscVBackend.wordToWordConf)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64)))))) :
    let source := labInitializedOriginal template stack backend
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
      (.const initial) (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))
      (.return (.const returned)) budget pan loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
        (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ ticks finalMachine finalFfi,
        ticks ≤ backend.successTickLimit wc riscvConfig
          (panToWordCompileProgHOL arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const initial) (.seq .skip
              (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
                (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine =
          (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  classical
  let source := labInitializedOriginal template stack backend
  let panCode := HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse
  let pan := noGlobalsLoweredPreCall source panCode
  let crepPrograms := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let crep := concreteDeclCrepState pan crepPrograms
  let target := {concreteDeclLoopState arch crep crepPrograms with memory := stack.memory}
  let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
  let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
    (.const initial) (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))
    (.return (.const returned)) budget pan loopCtxt .ln
  have preCall : pan = {labInitializedSource template stack backend with code := panCode} := by
    exact labInitializedOriginal_preCall template stack backend panCode clockPositive
  have memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs := by
    simpa [crep,target,pan,source,crepPrograms] using
      labInitializedOriginal_preCall_memoryRel template crepPrograms stack backend panCode clockPositive wordMemory
  have fields := labInitializedSource_fields template stack backend
  have panDomain : ∀ address, pan.memaddrs address ↔
      Flapjack.Compiler.Backend.StackRemove.addresses pan.baseAddr
        ((backend.labHeapLength.toNat / 8) + (backend.labHeapLength.toNat / 8)) address := by
    simpa [preCall] using fields.2.1
  have panShared : backend.lab.sharedMemDomain = (concreteDeclLoopState arch (concreteDeclCrepState pan crepPrograms) crepPrograms).shMdomain := by
    simpa [preCall,concreteDeclCrepState] using labInitializedSource_shared template crepPrograms arch stack backend
  have panClock : backend.lab.clock = pan.clock := by simpa [preCall] using fields.2.2.2.1.symm
  have panEndian : backend.lab.be = pan.be := by simpa [preCall] using fields.2.2.2.2.1.symm
  have panFfi : backend.lab.ffi = pan.ffi := by simpa [preCall] using fields.2.2.2.2.2.1.symm
  have panBase : backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word pan.baseAddr := by
    simpa [preCall] using fields.1
  have panHeap : pan.topAddr = pan.baseAddr + 2 * backend.labHeapLength := by simpa [preCall] using fields.2.2.1
  have assignmentShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL assignment) := by
    cases bodyShape with
    | assign _ _ _ shape => exact shape
  have compilerEq : panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const initial)
        (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))) =
      loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
    simpa only [singleDef,startDef] using
      (singleEntry_declaredWhile_panToWord arch (ofString name) initial returned (expToHOL condition) (expToHOL assignment) _ conditionShape assignmentShape)
  have programsEq' : programs = (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2 := by
    simpa only [compilerEq] using programsEq
  let native := sourceFullInitEmptyOracleInputs declarations start caller loopCtxt entry limit arch pan wc ac stack cfg
    callerEq loopContextEq programs programsEq' backend inputCodeEq bitmapPrefix registers stackOracle
    panDomain panShared panClock panEndian panFfi panBase panHeap
  have result := countdownZero_counted_fullCompiler_success declarations start [] emptyGlobalsContext caller
    condition assignment name initial context primitive handler functions conditionRanged assignmentRanged nameRanged fuel
    (labInitializedProduction production template stack backend) source pan pan crep
    (labInitializedProduction_rel production template stack backend environment ffiRel)
    (labInitializedProduction_ranged production template stack backend ranged)
    cost budget returned (by simpa [source,labInitializedOriginal] using sourceClock) budgetBound
    returnLocals returnGlobals returnMemory returnFfi returnValues wholeRun conditionShape bodyShape
    loopCtxt target arch rfl rfl (by simpa [source,labInitializedOriginal,labInitializedSource] using templateLocals)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateGlobals)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateExceptions)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateStructs)
    (labInitializedOriginal_top_outside template stack backend)
    (labInitializedOriginal_top_aligned template stack backend) startDef singleDef
    (by simpa [source,labInitializedOriginal,labInitializedSource] using sourceCode)
    rfl rfl rfl rfl memRel native (by simpa [native,sourceFullInitEmptyOracleInputs,sourceFullInitInputs,sourceCompilerInputs] using acEq)
    declarationsEq (by simpa [native,sourceFullInitEmptyOracleInputs,sourceFullInitInputs,sourceCompilerInputs] using archEq)
    (by simpa [native,sourceFullInitEmptyOracleInputs,sourceFullInitInputs,sourceCompilerInputs] using wcEq)
  simpa only [native,sourceFullInitEmptyOracleInputs,source,pan,panCode,entry,limit,crepPrograms] using result


/-- Set the proof clock from the source budget without changing the machine. -/
theorem countdownZero_labInitialized_withClock_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (arch : AsmArchitecture) (name : VarName) (initial returned : BitVec 64)
    (condition assignment : Exp (RiscV.Word 64)) (cost budget : Nat)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack)
    (cfg : LabToTarget.Config)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production) (ffiRel : FfiStateRel production.ffi backend.lab.ffi)
    (nameRanged : NameRanged name) (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (budgetBound : cost ≤ budget)
    (returnLocals returnGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnMemory : BitVec 64 → Option (PanValue (BitVec 64))) (returnFfi : FfiState σ)
    (returnValues : List (PanValue (RiscV.Word 64)))
    (wholeRun : let prod := labInitializedProduction production template stack backend
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+4)
        prod.locals prod.globals prod.memory prod.ffi
        (.dec name .one (.const initial) (.seq .skip (.seq
          (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) =
          some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost))
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (templateLocals : template.locals = HolFiniteMapExact.empty)
    (templateGlobals : template.globals = HolFiniteMapExact.empty)
    (templateExceptions : template.eshapes = HolFiniteMapExact.empty)
    (templateStructs : template.structs = [])
    (startDef : start = ofString "main")
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const initial)
      (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))
    (sourceCode : template.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const initial)
        (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))),.one)))
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const initial)
        (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))))).2)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], []))
    (wordMemory : ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word)
    (acEq : ac = riscvConfig) (archEq : arch = riscvConfig.isa)
    (wcEq : wc = countdownRiscVBackend.wordToWordConf)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64)))))) :
    let adjustedStack := (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode {backend.lab with clock := budget+1} backend.saveRegs backend.dataSp backend.coracle).1
    let adjusted := backend.withClock (budget+1)
    let source := labInitializedOriginal template adjustedStack adjusted
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
      (.const initial) (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))
      (.return (.const returned)) budget pan loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
        (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit wc riscvConfig
          (panToWordCompileProgHOL arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const initial) (.seq .skip
              (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
                (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine =
          (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  classical
  let adjusted := backend.withClock (budget+1)
  have clocks := labCounted_clock_from_budget stack backend condition assignment cost budget budgetBound
  have shiftedRun : let prod := labInitializedProduction production template _ adjusted
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+4)
        prod.locals prod.globals prod.memory prod.ffi
        (.dec name .one (.const initial) (.seq .skip (.seq
          (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) =
          some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost) := by
    dsimp only
    rw [show adjusted = backend.withClock (budget+1) from rfl, labInitializedProduction_counted_withClock]
    exact wholeRun
  have shiftedMemory : ∀ address, (labInitializedOriginal template _ adjusted).memaddrs address →
      ∃ word, adjusted.lab.memory address = .word word := by
    intro address member
    apply wordMemory address
    simpa [adjusted,FullInitMachineContext.withClock,labInitializedOriginal,labInitializedSource,
      FullInitMachineContext.labHeapLength] using member
  exact countdownZero_labInitialized_success declarations start caller loopCtxt arch name initial returned
    condition assignment cost budget context primitive handler functions fuel production template wc ac _ adjusted cfg
    environment ranged (by simpa [adjusted,FullInitMachineContext.withClock] using ffiRel)
    nameRanged conditionRanged assignmentRanged clocks.2.1 clocks.1 budgetBound
    returnLocals returnGlobals returnMemory returnFfi returnValues shiftedRun conditionShape bodyShape
    templateLocals templateGlobals templateExceptions templateStructs startDef singleDef sourceCode callerEq loopContextEq
    programs programsEq (by simpa [adjusted,FullInitMachineContext.withClock] using inputCodeEq)
    (by simpa [adjusted,FullInitMachineContext.withClock] using bitmapPrefix) registers
    (by simpa [adjusted,FullInitMachineContext.withClock] using stackOracle) shiftedMemory
    acEq archEq wcEq declarationsEq

end SteppedFlapjack.PanToCrepSteps
