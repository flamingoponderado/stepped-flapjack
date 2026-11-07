import SteppedFlapjack.PanToCrepSteps.CountdownGoodCode
import SteppedFlapjack.PanToCrepSteps.CountdownRiscVConfig
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi

/-! Construct the countdown's matching source environments from an arbitrary template. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps Flapjack.Misc
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

set_option maxHeartbeats 1000000 in
/-- The standard backend configuration derives the actual countdown Lab code-safety guard. -/
theorem labInit_countdown_backendConfig_riscv {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (config : Backend.Config) (hcfg : backendConfigOk riscvConfig config)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (cfg : LabToTarget.Config)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ) (code code2 : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat))
    (labelClock i cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (labOracle : Nat → LabToTarget.Config × LabSem.LabProgHOL 64)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hmc : mc.target = riscvTarget)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11) (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13)
    (oracleLabels : cfg.labels = labs) (oraclePos : cfg.pos = (progToBytes code2).length)
    (oracleFfi : cfg.ffiNames = some mc.ffiNames)
    (guards : LabMachineInitGuardsReduced mc machine code code2 labs labelClock i cbspace asm memory dm sdm
      newFfiNames shmemInfo newShmemInfo)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (stackInit : let programs := (compile config.wordToWordConf riscvConfig (panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))).2
      Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      config.stackConf config.dataConf (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1) (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false programs).1
      (Flapjack.Compiler.Backend.WordToStack.Native.compileNative riscvConfig false programs).2.2.2
      (LabToTarget.makeInit mc ffi asm memory dm sdm machine code (LabToTarget.compileLab mc.target.config)
        (mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length) cbspace labOracle)
      saveRegs dataSp (fun _ => (cfg,[],[]))) :
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
    let loopCtxt := mkCtxtExact riscvConfig.isa (makeVmapExact [])
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
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (adjusted.successTickLimit config.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) adjusted.resourceTickLimit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = adjustedStack.ffi.ioEvents))) := by
  have codeEq := stackInit.2.1
  have codeGood : goodCode mc.target.config (.ln : Spt (Spt Nat)) code := by
    rw [hmc]
    have compiled := countdown_compiled_goodCode (ofString name) (BitVec.ofNat 64 count) returned config mc hmc hcfg
    have codeEq' : code = StackToLab.compile config.stackConf config.dataConf
        (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
        (countdownNativeRiscV (ofString name) (BitVec.ofNat 64 count) returned config.wordToWordConf).2.2.2 := by
      simpa only [LabToTarget.makeInit,countdownNativeRiscV,countdownBodyHOL] using codeEq
    rw [codeEq']
    exact compiled
  have core := labMachineInitGuardsCore_of_reduced mc machine code code2 labs labelClock i cbspace asm memory dm sdm
    labOracle newFfiNames shmemInfo newShmemInfo codeGood guards
  exact labInit_countdown_riscvConfig_riscv name count budget returned context primitive handler functions fuel production template
    config.wordToWordConf config.stackConf config.dataConf (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1)
    (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset saveRegs dataSp cfg
    mc machine ffi code code2 labs labelClock i cbspace labClock asm memory dm sdm labOracle
    newFfiNames shmemInfo newShmemInfo hmc ptr len ptr2 len2 oracleLabels oraclePos oracleFfi core
    nameRanged wordRange budgetBound stackInit

end SteppedFlapjack.PanToCrepSteps
