import SteppedFlapjack.PanToCrepSteps.CountdownZeroCompiledSafe
import SteppedFlapjack.PanToCrepSteps.ExecutableCountdownRiscV
import SteppedFlapjack.PanToCrepSteps.ArtifactCountdownRiscV

/-! Successful execution of the actual compiler artifact. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps Flapjack.Misc
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

set_option maxHeartbeats 1000000 in
/-- A full executable compiler result supplies the code and bitmap premises. -/
theorem countdownZero_executableCompiler_success {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (dataSp : Nat)
    (final : Backend.Config) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (stackMax : Option Nat)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain : BitVec 64 → Bool)
    (hmc : isRiscvMachineConfig mc)
    (hcompile : compileProgMaxAsmExecutable countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        (some (bytes,bitmaps,final),stackMax))
    (hffi : final.labConf.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc machine bytes cbspace asm memory (countdownStackByteDomain countdownRiscVBackend asm bitmapsDomain) (fun _ => false))
    (noFfi : mc.ffiNames = []) (noMmio : mc.mmioInfo = [])
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend mc machine asm memory bitmapPtr bitmapsDomain bytes
      cbspace dataSp bitmaps)
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
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  obtain ⟨hlab,hbitmaps⟩ := countdown_executableCompiler_lab (ofString name) (BitVec.ofNat 64 count) returned
    mc hmc.1 bytes bitmaps final stackMax (by simpa only [countdownBodyHOL] using hcompile)
  exact countdownZero_riscvBackend_noFfi_success name count budget returned context primitive handler functions fuel production template
    dataSp final.labConf bytes mc machine ffi cbspace labClock asm memory bitmapPtr bitmapsDomain
    hmc hlab hffi hinit noFfi noMmio nameRanged wordRange budgetBound (by simpa only [hbitmaps] using layout)
    nameEq countEq returnedEq


set_option maxHeartbeats 1000000 in
/-- The artifact-only Pancake compiler supplies the full countdown runtime bound. -/
theorem countdownZero_artifactCompiler_success {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (dataSp : Nat)
    (final : Backend.Config) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain : BitVec 64 → Bool)
    (hmc : isRiscvMachineConfig mc)
    (hcompile : compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        some (bytes,bitmaps,final))
    (hffi : final.labConf.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc machine bytes cbspace asm memory (countdownStackByteDomain countdownRiscVBackend asm bitmapsDomain) (fun _ => false))
    (noFfi : mc.ffiNames = []) (noMmio : mc.mmioInfo = [])
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend mc machine asm memory bitmapPtr bitmapsDomain bytes
      cbspace dataSp bitmaps)
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
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let source := singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
    (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))
  let full := compileProgMaxAsmExecutable countdownRiscVBackend riscvConfig source
  have artifact : full.1 = some (bytes,bitmaps,final) := by
    simpa only [full,source,compileProgAsmFast_eq_fst] using hcompile
  have fullCompile : full = (some (bytes,bitmaps,final),full.2) := by
    exact Prod.ext artifact rfl
  exact countdownZero_executableCompiler_success name count budget returned context primitive handler functions fuel production template
    dataSp final bytes bitmaps full.2 mc machine ffi cbspace labClock asm memory bitmapPtr bitmapsDomain
    hmc (by simpa only [full,source] using fullCompile) hffi hinit noFfi noMmio nameRanged wordRange budgetBound layout
    nameEq countEq returnedEq

end SteppedFlapjack.PanToCrepSteps
