import SteppedFlapjack.PanToCrepSteps.FilteredCompiledCountdown
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

/-- The actual GC-free RISC-V backend used by the Pancake compiler. -/
noncomputable def countdownRiscVBackend : Backend.Config :=
  Flapjack.Compiler.pancakeBackendConf riscvBackendConfig

set_option maxHeartbeats 1000000 in
/-- The actual Pancake RISC-V backend satisfies its configuration premises. -/
theorem riscvBackend_countdown_compiled_riscv {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (dataSp : Nat)
    (cfg : LabToTarget.Config) (bytes : List (BitVec 8))
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain sharedDomain : BitVec 64 → Bool)
    (hmc : isRiscvMachineConfig mc)
    (hcompile : LabToTarget.compile riscvConfig countdownRiscVBackend.labConf
      (countdownStackLabCode (ofString name) (BitVec.ofNat 64 count) returned countdownRiscVBackend) = some (bytes,cfg))
    (hffi : cfg.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc machine bytes cbspace asm memory (countdownStackLabDomain countdownRiscVBackend asm bitmapsDomain) (fun a => sharedDomain a && holByteAligned a))
    (hentries : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      (cfg.shmemExtra.map (fun r => { r with
        entryPc := (mc.target.getPc machine).toNat+r.entryPc,
        exitPc := (mc.target.getPc machine).toNat+r.exitPc })).map ShmemInfoNum.entryPc =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      mc.mmioInfo = List.zip ((List.range cfg.shmemExtra.length).map (fun index => index+i))
        (cfg.shmemExtra.map (fun r => (r.nbytes,HolAddr.addr r.addrReg (BitVec.ofNat 64 r.addrOff),
          r.reg,BitVec.ofNat 64 ((mc.target.getPc machine).toNat+r.exitPc)))))
    (hbuffer : ∀ i, mmioPcsMinIndex mc.ffiNames = some i → ∀ bn, bn < cbspace →
      BitVec.ofNat 64 bn + BitVec.ofNat 64 bytes.length + mc.target.getPc machine ∉ mc.ffiEntryPcs.take i)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend mc machine asm memory bitmapPtr bitmapsDomain bytes
      cbspace dataSp (countdownNativeRiscV (ofString name) (BitVec.ofNat 64 count) returned countdownRiscVBackend.wordToWordConf).1) :
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
        ticks ≤ max (adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) adjusted.resourceTickLimit ∧
        evaluateTargetHOL mc ffi ticks machine = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = adjustedStack.ffi.ioEvents))) := by
  have provided : ∀ ffis, countdownRiscVBackend.labConf.ffiNames = some ffis →
      ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s := by
    intro ffis h
    change none = some ffis at h
    cases h
  exact filteredCompiled_countdown_riscv name count budget returned context primitive handler functions fuel production template
    countdownRiscVBackend riscvPancakeBackendConfigOk dataSp cfg bytes mc machine ffi cbspace labClock asm memory
    bitmapPtr bitmapsDomain sharedDomain hmc.1 (riscvPancakeInitOk mc hmc) hmc.2.2.1 hmc.2.1 hmc.2.2.2.2.1 hmc.2.2.2.1
    hcompile provided hffi hinit hentries hmmio hbuffer nameRanged wordRange budgetBound layout

end SteppedFlapjack.PanToCrepSteps
