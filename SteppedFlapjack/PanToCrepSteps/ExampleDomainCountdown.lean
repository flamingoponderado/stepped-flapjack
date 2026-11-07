import SteppedFlapjack.PanToCrepSteps.ConcreteStateCountdown
import SteppedFlapjack.PanToCrepSteps.CountdownCodeMemory
import SteppedFlapjack.PanToCrepSteps.CountdownNoFfi
import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import SteppedFlapjack.PanToCrepSteps.CountdownExecutableCompiler
import Flapjack.Compiler.Backend.LabToTarget.ShmemMembership
import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards
import SteppedFlapjack.PanToCrepSteps.CountdownRiscVConfig
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi

/-! Specialize the countdown bound to fixed domains and coherent byte/word memory. -/
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
/-- Countdown bound with fixed heap and bitmap domains, concrete registers, and
byte memory constructed from words. The emitted code must fit below the heap. -/
theorem exampleDomain_countdown_riscv {σ : Type}
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
 :
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
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (adjusted.successTickLimit countdownRiscVBackend.wordToWordConf riscvConfig
          (panToWordCompileProgHOL riscvConfig.isa (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) adjusted.resourceTickLimit ∧
        evaluateTargetHOL countdownMachineConfig ffi ticks (countdownMachineState (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs) = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = adjustedStack.ffi.ioEvents))) := by
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
  exact concreteState_countdown_riscv name count budget returned context primitive handler functions fuel production template
    8191 final bytes [4] (countdownBytesOfWords (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)))) countdownExampleRegs ffi cbspace labClock (fun x => WordLocW.word ((countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))) x)) 131072 countdownExampleBitmapsDomain
    hcompile hffi (countdownExample_codeLoaded bytes cbspace 4 initial fits) domain closed (countdownBytesOfWords_consistent (countdownExampleWords bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))))
    (countdownExample_buffer _ bytes cbspace fits) (by omega) nameRanged wordRange budgetBound (countdownExample_stackLayout bytes cbspace 8191 [4] (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial))
      (by simpa using countdownExample_singleBitmapLayout (countdownExampleBitmapBacking 4 (countdownWriteCode 4096 bytes initial)) 4 (by simp [countdownExampleBitmapBacking])))

end SteppedFlapjack.PanToCrepSteps
