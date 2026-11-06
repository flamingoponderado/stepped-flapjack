import SteppedFlapjack.PanToCrepSteps.LabInitializedCountdown
import SteppedFlapjack.PanToCrepSteps.CountedCountdownFullInit

/-! Full-initialization RISC-V bound for the Lab-derived countdown source. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A Lab-derived countdown source has the explicit full-initialization
RISC-V tick bound, with successful return or entry resource exhaustion. -/
theorem labInitialized_countdown_fullInit_riscv {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (arch : AsmArchitecture) (name : VarName) (count budget : Nat) (returned : BitVec 64)
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
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (sourceClock : count ≤ backend.lab.clock - 1) (clockPositive : 0 < backend.lab.clock)
    (budgetBound : 6*count+9 ≤ budget)
    (templateLocals : template.locals = HolFiniteMapExact.empty)
    (templateGlobals : template.globals = HolFiniteMapExact.empty)
    (templateExceptions : template.eshapes = HolFiniteMapExact.empty)
    (templateStructs : template.structs = [])
    (topOutside : ¬ (labInitializedOriginal template stack backend).memaddrs (labInitializedOriginal template stack backend).topAddr)
    (aligned : panGlobalsByteAlignedHOL (labInitializedOriginal template stack backend).topAddr)
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
      (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))))
    (sourceCode : template.code = HolFiniteMapExact.empty.update
      (newMainNameHOL declarations,([],(.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))),.one)))
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], []))
    (wordMemory : ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word) :
    let source := labInitializedOriginal template stack backend
    let prod := labInitializedProduction production template stack backend
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declaredAssignLoopLimit declarations [] emptyGlobalsContext caller
      (.var .local name : Exp (RiscV.Word 64)) (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))
      name (BitVec.ofNat 64 count) returned pan budget loopCtxt .ln
    ∃ sourceResult,
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        prod.locals prod.globals prod.memory prod.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
          (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) = some (sourceResult,6*count+9) ∧
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name)
          (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))) =
        (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (backend.successTickLimit wc ac
          (loopToWordCompileHOL (compileProgHOLExact arch (compileProgDeclsHOLW (compileTopExactHOL declarations start))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) backend.resourceTickLimit ∧
        evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = stack.ffi.ioEvents))) := by
  classical
  let source := labInitializedOriginal template stack backend
  let panCode := HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse
  let pan := noGlobalsLoweredPreCall source panCode
  let crepPrograms := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let crep := concreteDeclCrepState pan crepPrograms
  let target := {concreteDeclLoopState arch crep crepPrograms with memory := stack.memory}
  let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
  let limit := declaredAssignLoopLimit declarations [] emptyGlobalsContext caller
    (.var .local name : Exp (RiscV.Word 64)) (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))
    name (BitVec.ofNat 64 count) returned pan budget loopCtxt .ln
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
  let native := sourceFullInitEmptyOracleInputs declarations start caller loopCtxt entry limit arch pan wc ac stack cfg
    callerEq loopContextEq programs programsEq backend inputCodeEq bitmapPrefix registers stackOracle
    panDomain panShared panClock panEndian panFfi panBase panHeap
  have result := counted_singleEntry_countdown_fullInit_riscv declarations start [] emptyGlobalsContext caller
    name context primitive handler functions nameRanged fuel
    (labInitializedProduction production template stack backend) source pan pan crep
    (labInitializedProduction_rel production template stack backend environment ffiRel)
    (labInitializedProduction_ranged production template stack backend ranged)
    count budget returned wordRange (by simpa [source,labInitializedOriginal] using sourceClock) budgetBound
    loopCtxt target arch rfl rfl (by simpa [source,labInitializedOriginal,labInitializedSource] using templateLocals)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateGlobals)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateExceptions)
    (by simpa [source,labInitializedOriginal,labInitializedSource] using templateStructs)
    topOutside aligned singleDef (by simpa [source,labInitializedOriginal,labInitializedSource] using sourceCode)
    rfl rfl rfl rfl memRel native
  obtain ⟨sourceResult,_,sourceExec,_,_,_⟩ := labInitialized_countdown count production template stack backend
    environment ranged ffiRel name nameRanged wordRange sourceClock returned
    (ctxtFcExactHOL caller.funcs caller.eids [] [] []) context primitive handler functions fuel
  refine ⟨sourceResult,sourceExec,?_⟩
  simpa only [native,sourceFullInitEmptyOracleInputs,source,pan,panCode,entry,limit,crepPrograms] using result

end SteppedFlapjack.PanToCrepSteps
