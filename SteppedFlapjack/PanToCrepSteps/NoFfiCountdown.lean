import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
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

/-- The shared-memory extractor appends one name for each information record,
even before code-validity properties are established. -/
theorem shmemInfo_lengths (code : LabSem.LabProgHOL 64) (pos : Nat)
    (names : List HolFfiName) (info : List ShmemInfoNum) (hlen : names.length = info.length) :
    (getShmemInfo code pos names info).1.length = (getShmemInfo code pos names info).2.length := by
  induction code generalizing pos names info with
  | nil => simpa [getShmemInfo] using hlen
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos names info with
    | nil => simpa only [getShmemInfo] using ih pos names info hlen
    | cons line lines ihLines =>
      cases line with
      | label a b n => simpa only [getShmemInfo] using ihLines pos names info hlen
      | labAsm a w bs n => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
      | asm a bs n =>
        cases a with
        | asmi a => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
        | cbw a b => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
        | shareMem m r addr =>
          cases addr with
          | addr base off =>
            rcases hm : getMemopInfo m with ⟨op,nb⟩
            let entry : ShmemInfoNum :=
              { entryPc := pos, nbytes := nb, addrReg := base, addrOff := off.toNat,
                reg := r, exitPc := pos+bs.length }
            simpa only [getShmemInfo,hm,entry] using
              ihLines (pos+bs.length) (names++[.sharedMem op]) (info++[entry]) (by simp [hlen])

set_option maxHeartbeats 1000000 in
/-- An empty machine FFI interface discharges all MMIO and buffer exclusions. -/
theorem riscvBackend_countdown_noFfi_riscv {σ : Type}
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
    (noFfi : mc.ffiNames = []) (noMmio : mc.mmioInfo = [])
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
  obtain ⟨i,code2,labs,hindex,_,_,_,_,_,_,hdrop,hinfo⟩ :=
    countdown_labCompilation_ffi (ofString name) (BitVec.ofNat 64 count) returned countdownRiscVBackend
      riscvPancakeBackendConfigOk bytes cfg mc.ffiNames hcompile provided hffi
  have namesEmpty : (getShmemInfo code2 0 [] []).1 = [] := by
    simpa [noFfi] using hdrop.symm
  have lengths := shmemInfo_lengths code2 0 [] [] rfl
  have infoEmpty : (getShmemInfo code2 0 [] []).2 = [] := by
    have : (getShmemInfo code2 0 [] []).2.length = 0 := by simpa [namesEmpty] using lengths.symm
    exact List.length_eq_zero_iff.mp this
  have shmemEmpty : cfg.shmemExtra = [] := by simpa only [infoEmpty] using hinfo
  have start : startPcOk mc (mc.target.getPc machine) := by
    rw [← hinit.2.2.1]
    exact hinit.2.2.2.1
  have entriesEmpty : mc.ffiEntryPcs = [] := by
    have lengths := startPcOk_lengths start
    have : mc.ffiEntryPcs.length = 0 := by simpa [noFfi] using lengths.symm
    exact List.length_eq_zero_iff.mp this
  have entries : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      (cfg.shmemExtra.map (fun r => { r with
        entryPc := (mc.target.getPc machine).toNat+r.entryPc,
        exitPc := (mc.target.getPc machine).toNat+r.exitPc })).map ShmemInfoNum.entryPc =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i := by
    intro i _
    simp [shmemEmpty,entriesEmpty]
  have mmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      mc.mmioInfo = List.zip ((List.range cfg.shmemExtra.length).map (fun index => index+i))
        (cfg.shmemExtra.map (fun r => (r.nbytes,HolAddr.addr r.addrReg (BitVec.ofNat 64 r.addrOff),
          r.reg,BitVec.ofNat 64 ((mc.target.getPc machine).toNat+r.exitPc)))) := by
    intro i _
    simp [shmemEmpty,noMmio]
  have buffer : ∀ i, mmioPcsMinIndex mc.ffiNames = some i → ∀ bn, bn < cbspace →
      BitVec.ofNat 64 bn + BitVec.ofNat 64 bytes.length + mc.target.getPc machine ∉ mc.ffiEntryPcs.take i := by
    simp [entriesEmpty]
  exact riscvBackend_countdown_compiled_riscv name count budget returned context primitive handler functions fuel production template
    dataSp cfg bytes mc machine ffi cbspace labClock asm memory bitmapPtr bitmapsDomain sharedDomain
    hmc hcompile hffi hinit entries mmio buffer nameRanged wordRange budgetBound layout

end SteppedFlapjack.PanToCrepSteps
