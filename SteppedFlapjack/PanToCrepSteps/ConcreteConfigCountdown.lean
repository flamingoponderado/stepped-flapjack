import SteppedFlapjack.PanToCrepSteps.ArtifactCountdownRiscV
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import SteppedFlapjack.PanToCrepSteps.CountdownExecutableCompiler
import Flapjack.Compiler.Backend.LabToTarget.ShmemMembership
import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards
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

open Flapjack.Compiler.Backend.RiscVConfig

open Flapjack.Pancake.Proofs.PanToTarget

set_option maxHeartbeats 1000000 in
/-- The countdown bound for an explicit empty-FFI RISC-V machine configuration. -/
theorem concreteConfig_countdown_riscv {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (dataSp : Nat)
    (final : Backend.Config) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain sharedDomain : BitVec 64 → Bool)
    (hcompile : compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        some (bytes,bitmaps,final))
    (hffi : final.labConf.ffiNames = some countdownMachineConfig.ffiNames)
    (hinit : goodInitState countdownMachineConfig machine bytes cbspace asm memory (countdownStackLabDomain countdownRiscVBackend asm bitmapsDomain) (fun a => sharedDomain a && holByteAligned a))
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend countdownMachineConfig machine asm memory bitmapPtr bitmapsDomain bytes
      cbspace dataSp bitmaps) :
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
    backend.mc = countdownMachineConfig ∧ backend.machine = machine ∧
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
        ticks ≤ max (adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) adjusted.resourceTickLimit ∧
        evaluateTargetHOL countdownMachineConfig ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = adjustedStack.ffi.ioEvents))) := by
  exact artifactCompiler_countdown_noFfi_riscv name count budget returned context primitive handler functions fuel production template
    dataSp final bytes bitmaps countdownMachineConfig machine ffi cbspace labClock asm memory bitmapPtr bitmapsDomain sharedDomain
    countdownMachineConfig_fields.1 hcompile hffi hinit countdownMachineConfig_fields.2.1 countdownMachineConfig_fields.2.2
    nameRanged wordRange budgetBound layout

end SteppedFlapjack.PanToCrepSteps
