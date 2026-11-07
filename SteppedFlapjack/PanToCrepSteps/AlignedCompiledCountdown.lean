import SteppedFlapjack.PanToCrepSteps.AlignedCountdownCanonical
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

/-- Byte-addressed heap and bitmap domain before word alignment. -/
noncomputable def countdownStackByteDomain (config : Backend.Config) (asm : AsmState 64)
    (bitmapsDomain : BitVec 64 → Bool) : BitVec 64 → Bool :=
  fun a => decide (asm.regs (StackNames.findNameSpt config.stackConf.regNames 2) ≤ a ∧
    a < asm.regs (StackNames.findNameSpt config.stackConf.regNames 4)) || bitmapsDomain a

set_option maxHeartbeats 1000000 in
/-- The counted countdown bound with byte-domain machine initialization and
word-aligned Stack initialization connected by a same-clock simulation. -/
theorem alignedCompiled_countdown_riscv {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (config : Backend.Config) (hcfg : backendConfigOk riscvConfig config)
    (dataSp : Nat)
    (cfg : LabToTarget.Config) (bytes : List (BitVec 8))
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (machine : RiscV.L3.riscv_state)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat) (asm : AsmState 64)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain : BitVec 64 → Bool)
    (hmc : mc.target = riscvTarget)
    (hmcInit : mcInitOk riscvConfig config mc)
    (ptr : mc.ptrReg = 10) (len : mc.lenReg = 11) (ptr2 : mc.ptr2Reg = 12) (len2 : mc.len2Reg = 13)
    (hcompile : LabToTarget.compile riscvConfig config.labConf
      (countdownStackLabCode (ofString name) (BitVec.ofNat 64 count) returned config) = some (bytes,cfg))
    (hprovided : ∀ ffis, config.labConf.ffiNames = some ffis →
      ∀ n ∈ ffis, ∃ s, n = HolFfiName.extCall s)
    (hffi : cfg.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc machine bytes cbspace asm memory (countdownStackByteDomain config asm bitmapsDomain) (fun _ => false))
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
    (layout : countdownStackMemoryLayout config mc machine asm memory bitmapPtr bitmapsDomain bytes
      cbspace dataSp (countdownNativeRiscV (ofString name) (BitVec.ofNat 64 count) returned config.wordToWordConf).1) :
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
  obtain ⟨i,code2,labs,hbytes,guards⟩ := countdown_filteredLab_guards (ofString name) (BitVec.ofNat 64 count)
    returned config mc machine asm memory (countdownStackByteDomain config asm bitmapsDomain)
    (fun _ => false) cbspace bytes cfg hmc hcfg ptr len ptr2 len2
    hcompile hprovided hffi hinit hentries hmmio hbuffer
  have stackInit := countdown_stackInit_from_memory (ofString name) (BitVec.ofNat 64 count) returned config mc machine ffi asm memory
    bitmapPtr bitmapsDomain (fun _ => false) bytes cbspace dataSp cfg (LabToTarget.compile mc.target.config)
    hmc hcfg hmcInit ptr len ptr2 len2 layout
  have result := alignedLabInit_countdown_canonicalSource_riscv riscvConfig.isa name count budget returned
    context primitive handler functions fuel production template config.wordToWordConf riscvConfig config.stackConf config.dataConf
    (2 * DataToWord.maxHeapLimit 64 config.dataConf - 1) (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3))
    riscvConfig.addrOffset (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp cfg mc machine ffi
    (countdownStackLabCode (ofString name) (BitVec.ofNat 64 count) returned config) code2 labs config.labConf.initClock i cbspace labClock
    asm memory (countdownStackByteDomain config asm bitmapsDomain) (fun _ => false)
    (countdownStackLabOracle config cfg) _ _ _ hmc guards nameRanged wordRange budgetBound riscvConfig_native_registers
    (by
      rw [hbytes] at stackInit
      change StackToLab.Proofs.FullMakeInitSemantics.Assumptions _ _ _ _ _ _ _
        (LabToTarget.makeInit mc ffi asm memory
          (fun a => (decide (asm.regs (StackNames.findNameSpt config.stackConf.regNames 2) ≤ a ∧
            a < asm.regs (StackNames.findNameSpt config.stackConf.regNames 4)) || bitmapsDomain a) && holByteAligned a)
          (fun a => false && holByteAligned a) machine _ _ _ _ _) _ _ _
      exact stackInit)
  exact result

end SteppedFlapjack.PanToCrepSteps
