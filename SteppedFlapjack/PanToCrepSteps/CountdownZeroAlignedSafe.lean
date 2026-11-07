import SteppedFlapjack.PanToCrepSteps.CountdownZeroGeneralSafe
import SteppedFlapjack.PanToCrepSteps.AlignedCountdownLabInit

/-! Success-only bound from the aligned Lab initializer. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps Flapjack.Misc
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

set_option maxHeartbeats 1000000 in
/-- Derive the counted countdown machine bound from the Lab and Stack initializer guards,
constructing the native code, bitmaps, no-install oracle and source word memory. -/
theorem countdownZero_alignedLabInit_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (arch : AsmArchitecture) (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (saveRegs : Nat → Bool) (dataSp : Nat)
    (cfg : LabToTarget.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ) (code code2 : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (labOracle : Nat → LabToTarget.Config × LabSem.LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (guards : LabMachineInitGuards mc machine (LabFilter.filterSkip code) code2 labs labelClock i cbspace asm memory dm sdm
      (fun n => ((labOracle n).1,LabFilter.filterSkip (labOracle n).2)) newFfiNames shmemInfo newShmemInfo)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production) (ffiRel : FfiStateRel production.ffi ffi)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (templateLocals : template.locals = HolFiniteMapExact.empty)
    (templateGlobals : template.globals = HolFiniteMapExact.empty)
    (templateExceptions : template.eshapes = HolFiniteMapExact.empty)
    (templateStructs : template.structs = [])
    (startDef : start = ofString "main")
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))
    (sourceCode : template.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))),.one)))
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackInit : let programs := (compile wc ac (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))).2
      Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      stackConf dataConf maxHeap sp offset
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2
      (LabToTarget.makeInit mc ffi asm memory (fun a => dm a && holByteAligned a) sdm machine code (LabToTarget.compile mc.target.config)
        (mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp (fun _ => (cfg,[],[])))
    (acEq : ac = riscvConfig) (archEq : arch = riscvConfig.isa)
    (wcEq : wc = countdownRiscVBackend.wordToWordConf)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64)))))) :
    let caller := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
    let loopCtxt := mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0
    ∃ (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack),
    backend.mc = mc ∧ backend.machine = machine ∧
    let adjustedStack := (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode {backend.lab with clock := budget+1} backend.saveRegs backend.dataSp backend.coracle).1
    let adjusted := backend.withClock (budget+1)
    let source := labInitializedOriginal template adjustedStack adjusted
    let prod := labInitializedProduction production template stack backend
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
      (.const (BitVec.ofNat 64 count)) (.var .local (ofString name)) (countdownBodyHOL name)
      (.return (.const returned)) budget pan loopCtxt .ln
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
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit wc riscvConfig
          (panToWordCompileProgHOL arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let caller := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  let loopCtxt := mkCtxtExact arch (makeVmapExact [])
    (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0
  let programs := (compile wc ac (panToWordCompileProgHOL arch
    (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))).2
  obtain ⟨stack,backend,inputEq,bitmaps,oracle,mcEq,machineEq,clockEq,ffiEq,memoryEq,wordMemory⟩ :=
    alignedLabInit_native_compiler_source_inputs stackConf dataConf maxHeap sp offset saveRegs dataSp ac programs cfg
      mc machine ffi code code2 labs labelClock i cbspace labClock asm memory dm sdm labOracle
      newFfiNames shmemInfo newShmemInfo hmc guards stackInit template
  refine ⟨stack,backend,mcEq,machineEq,?_⟩
  have result := countdownZero_fromGeneral_withClock_success declarations start caller loopCtxt arch
    name count budget returned context primitive handler functions fuel production template wc ac stack backend cfg
    environment ranged (by simpa only [ffiEq] using ffiRel) nameRanged wordRange budgetBound
    templateLocals templateGlobals templateExceptions templateStructs startDef singleDef sourceCode rfl rfl
    programs rfl inputEq bitmaps registers oracle wordMemory acEq archEq wcEq declarationsEq
  simpa only [mcEq,machineEq,ffiEq] using result


set_option maxHeartbeats 1000000 in
/-- The counted countdown bound constructs matching empty source environments and its code table. -/
theorem countdownZero_alignedCanonical_success {σ : Type}
    (arch : AsmArchitecture) (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (saveRegs : Nat → Bool) (dataSp : Nat)
    (cfg : LabToTarget.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ) (code code2 : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (labOracle : Nat → LabToTarget.Config × LabSem.LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (guards : LabMachineInitGuards mc machine (LabFilter.filterSkip code) code2 labs labelClock i cbspace asm memory dm sdm
      (fun n => ((labOracle n).1,LabFilter.filterSkip (labOracle n).2)) newFfiNames shmemInfo newShmemInfo)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackInit : let programs := (compile wc ac (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))).2
      Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      stackConf dataConf maxHeap sp offset
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2
      (LabToTarget.makeInit mc ffi asm memory (fun a => dm a && holByteAligned a) sdm machine code (LabToTarget.compile mc.target.config)
        (mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp (fun _ => (cfg,[],[])))
    (acEq : ac = riscvConfig) (archEq : arch = riscvConfig.isa)
    (wcEq : wc = countdownRiscVBackend.wordToWordConf)
    (nameEq : name = "x") (countEq : count = 0) (returnedEq : returned = 0) :
    let body : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
    let start := ofString "main"
    let declarations := singleEntryProgram start body
    let sourceTemplate := singleEntrySourceTemplate template (newMainNameHOL declarations) body
    let productionFfi := {production with ffi := sourceFfiState ffi}
    let sourceProduction := singleEntrySourceProduction productionFfi (newMainNameHOL declarations) body
    let caller := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
    let loopCtxt := mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0
    ∃ (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack),
    backend.mc = mc ∧ backend.machine = machine ∧
    let adjustedStack := (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode {backend.lab with clock := budget+1} backend.saveRegs backend.dataSp backend.coracle).1
    let adjusted := backend.withClock (budget+1)
    let source := labInitializedOriginal sourceTemplate adjustedStack adjusted
    let prod := labInitializedProduction sourceProduction sourceTemplate stack backend
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
      (.const (BitVec.ofNat 64 count)) (.var .local (ofString name)) (countdownBodyHOL name)
      (.return (.const returned)) budget pan loopCtxt .ln
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
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit wc riscvConfig
          (panToWordCompileProgHOL arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let body : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
    (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))
  let start := ofString "main"
  let declarations := singleEntryProgram start body
  let sourceTemplate := singleEntrySourceTemplate template (newMainNameHOL declarations) body
  let productionFfi := {production with ffi := sourceFfiState ffi}
  let sourceProduction := singleEntrySourceProduction productionFfi (newMainNameHOL declarations) body
  have result := countdownZero_alignedLabInit_success declarations start arch name count budget returned
    context primitive handler functions fuel sourceProduction sourceTemplate wc ac stackConf dataConf maxHeap sp offset
    saveRegs dataSp cfg mc machine ffi code code2 labs labelClock i cbspace labClock asm memory dm sdm labOracle
    newFfiNames shmemInfo newShmemInfo hmc guards
    (singleEntrySource_environment productionFfi template (newMainNameHOL declarations) body)
    (singleEntrySource_ranged productionFfi (newMainNameHOL declarations) body)
    (by simpa [sourceProduction,singleEntrySourceProduction,productionFfi] using sourceFfiState_rel ffi) nameRanged wordRange budgetBound
    rfl rfl rfl rfl rfl rfl (by rfl) registers stackInit acEq archEq wcEq
    (by simp [declarations,body,start,nameEq,countEq,returnedEq,countdownBodyHOL])
  simpa only [sourceTemplate,sourceProduction,productionFfi,body,start,declarations] using result

end SteppedFlapjack.PanToCrepSteps
