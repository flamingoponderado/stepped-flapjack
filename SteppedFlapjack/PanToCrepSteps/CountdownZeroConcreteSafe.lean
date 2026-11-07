import SteppedFlapjack.PanToCrepSteps.CountdownZeroArtifactSafe
import SteppedFlapjack.PanToCrepSteps.ConcreteConfigCountdown
import SteppedFlapjack.PanToCrepSteps.ConcreteStateCountdown
import SteppedFlapjack.PanToCrepSteps.ExampleDomainCountdown

/-! Successful zero-count execution from concrete RISC-V initialization. -/
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
/-- The countdown bound for an explicit empty-FFI RISC-V machine configuration. -/
theorem countdownZero_concreteConfig_success {σ : Type}
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
    (bitmapsDomain : BitVec 64 → Bool)
    (hcompile : compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        some (bytes,bitmaps,final))
    (hffi : final.labConf.ffiNames = some countdownMachineConfig.ffiNames)
    (hinit : goodInitState countdownMachineConfig machine bytes cbspace asm memory (countdownStackByteDomain countdownRiscVBackend asm bitmapsDomain) (fun _ => false))
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend countdownMachineConfig machine asm memory bitmapPtr bitmapsDomain bytes
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
      ∃ ticks finalMachine finalFfi,
        ticks ≤ adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
        evaluateTargetHOL countdownMachineConfig ffi ticks machine = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  exact countdownZero_artifactCompiler_success name count budget returned context primitive handler functions fuel production template
    dataSp final bytes bitmaps countdownMachineConfig machine ffi cbspace labClock asm memory bitmapPtr bitmapsDomain
    countdownMachineConfig_fields.1 hcompile hffi hinit countdownMachineConfig_fields.2.1 countdownMachineConfig_fields.2.2
    nameRanged wordRange budgetBound layout nameEq countEq returnedEq


set_option maxHeartbeats 1000000 in
/-- The corrected bound for explicit RISC-V and assembler states. -/
theorem countdownZero_concreteState_success {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (dataSp : Nat)
    (final : Backend.Config) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (mem : BitVec 64 → BitVec 8) (regs : BitVec 5 → BitVec 64)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat)
    (memory : BitVec 64 → WordLocW 64) (bitmapPtr : BitVec 64)
    (bitmapsDomain : BitVec 64 → Bool)
    (hcompile : compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        some (bytes,bitmaps,final))
    (hffi : final.labConf.ffiNames = some countdownMachineConfig.ffiNames)
    (loaded : bytesInMemHOL 4096 bytes mem countdownMachineConfig.progAddresses
      (fun a => countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain a = true))
    (domain : ∀ a, countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain a = true →
      countdownMachineConfig.progAddresses a)
    (closed : ∀ a, countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain (holByteAlign a) = true →
      countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain a = true)
    (wordsOk : ∀ a, ∃ w, mem a = HolByte.getByte a w false ∧ memory (holByteAlign a) = .word w)
    (buffer : ∀ n, n < cbspace → countdownMachineConfig.progAddresses (BitVec.ofNat 64 (n+bytes.length)+4096) ∧
      countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain
        (BitVec.ofNat 64 (n+bytes.length)+4096) ≠ true)
    (size : cbspace+bytes.length < 2^64)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (layout : countdownStackMemoryLayout countdownRiscVBackend countdownMachineConfig (countdownMachineState mem regs) (countdownAsmState mem regs) memory bitmapPtr bitmapsDomain bytes
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
    backend.mc = countdownMachineConfig ∧ backend.machine = (countdownMachineState mem regs) ∧
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
        evaluateTargetHOL countdownMachineConfig ffi ticks (countdownMachineState mem regs) =
          (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  have hinit := countdownMachineState_goodInit mem regs memory
    (countdownStackByteDomain countdownRiscVBackend (countdownAsmState mem regs) bitmapsDomain)
    bytes cbspace loaded domain closed wordsOk buffer size
  exact countdownZero_concreteConfig_success name count budget returned context primitive handler functions fuel production template
    dataSp final bytes bitmaps (countdownMachineState mem regs) ffi cbspace labClock (countdownAsmState mem regs)
    memory bitmapPtr bitmapsDomain hcompile hffi hinit nameRanged wordRange budgetBound layout nameEq countEq returnedEq

set_option maxHeartbeats 1000000 in
/-- Countdown bound with fixed heap and bitmap domains, concrete registers, and
byte memory constructed from words. The emitted code must fit below the heap. -/
theorem countdownZero_exampleDomain_success {σ : Type}
    (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (final : Backend.Config) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (initial : BitVec 64 → BitVec 64)
    (ffi : HolFfiState σ)
    (cbspace labClock : Nat)
    (hcompile : compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) =
        some (bytes,bitmaps,final))
    (fits : bytes.length + cbspace ≤ 61440)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
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
    final.labConf.shmemExtra = [] ∧
    ∃ (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack),
    backend.mc = countdownMachineConfig ∧ backend.machine = (countdownMachineState (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs) ∧
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
        evaluateTargetHOL countdownMachineConfig ffi ticks (countdownMachineState (countdownBytesOfWords
          (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4
            (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs) = (.halt .success,finalMachine,finalFfi) ∧
        finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  have hffi : final.labConf.ffiNames = some countdownMachineConfig.ffiNames := by
    simpa [countdownMachineConfig] using countdown_artifact_emptyFfi (ofString name) (BitVec.ofNat 64 count) returned bytes bitmaps final (by simpa [countdownBodyHOL] using hcompile)
  have noShared := (countdown_artifact_noSharedMetadata (ofString name) (BitVec.ofNat 64 count) returned bytes bitmaps final (by simpa [countdownBodyHOL] using hcompile)).1
  refine ⟨noShared, ?_⟩
  have bm : bitmaps = [4] := countdown_artifact_bitmap_exact (ofString name) (BitVec.ofNat 64 count) returned bytes bitmaps final (by simpa [countdownBodyHOL] using hcompile)
  subst bitmaps
  have domain : ∀ a, countdownStackByteDomain countdownRiscVBackend (countdownAsmState (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs)
      countdownExampleBitmapsDomain a = true → countdownMachineConfig.progAddresses a := by
    rw [countdownExampleByteDomain_eq]
    intro a ha
    exact countdownExampleByteDomain_facts.2 a ha
  have closed : ∀ a, countdownStackByteDomain countdownRiscVBackend (countdownAsmState (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs)
      countdownExampleBitmapsDomain (holByteAlign a) = true →
      countdownStackByteDomain countdownRiscVBackend (countdownAsmState (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs)
        countdownExampleBitmapsDomain a = true := by
    rw [countdownExampleByteDomain_eq]
    exact countdownExampleByteDomain_closed
  exact countdownZero_concreteState_success name count budget returned context primitive handler functions fuel production template
    8191 final bytes [4] (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs ffi cbspace labClock (fun x => WordLocW.word ((countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))) x)) 131072 countdownExampleBitmapsDomain
    hcompile hffi (countdownExample_codeLoaded bytes cbspace 4 initial fits) domain closed (countdownBytesOfWords_consistent (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))))
    (countdownExample_buffer _ bytes cbspace fits) (by omega) nameRanged wordRange budgetBound (countdownExample_stackLayout bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))
      (by simpa using countdownExample_singleBitmapLayout (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)) 4 (by simp [countdownExampleBitmapBacking]))) nameEq countEq returnedEq

end SteppedFlapjack.PanToCrepSteps
