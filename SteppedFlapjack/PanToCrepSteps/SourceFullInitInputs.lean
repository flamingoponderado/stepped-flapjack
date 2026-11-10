import SteppedFlapjack.PanToCrepSteps.SourceNativeInputs
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs
import SteppedFlapjack.LoopToWordSteps.FullInitNativeValidity
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts

/-! Build source compiler inputs using full initialization. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Construct source compiler and full-initialization inputs from actual
compiled code, bitmap/oracle compatibility, and source–Stack data equalities. -/
noncomputable def sourceFullInitInputs {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (entry : HolLoopProg 64) (limit : Nat) (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (heapLength : BitVec 64)
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2)
    (backend : FullInitMachineContext stack)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (oracleValid : ∀ n,
      let ((bm0, _), progs) := coracle n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = backend.bitmaps.length))
    (oracleEq : backend.coracle = (fun n =>
      let ((bm0,cfg),progs) := coracle n
      let (compiled,_,bm) := Flapjack.Compiler.Backend.WordToStack.Native.compileWordToStackNative ac false
        (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (cfg,compiled,appListAppend bm.1)))
    (memory : stack.memory = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).memory)
    (domain : stack.mdomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).mdomain)
    (shared : stack.shMdomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).shMdomain)
    (clock : stack.clock = source.clock) (endian : stack.be = source.be) (ffi : stack.ffi = source.ffi)
    (current : stack.store.lookup .currHeap = some (.word source.baseAddr))
    (length : stack.store.lookup .heapLength = some (.word heapLength))
    (heap : source.topAddr = source.baseAddr + 2 * heapLength)
 :
    FullInitAssignLoopInputs declarations start caller loopCtxt entry limit
      (concreteDeclLoopState arch (concreteDeclCrepState source
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
  have codeFacts := backend.nativeCompilerCode ac programs inputCodeEq bitmapPrefix
  have ok := backend.nativeInitOk_of_compiled ac programs coracle registers bitmapPrefix oracleValid oracleEq
  have codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2 := by
    simpa only [programsEq] using codeFacts.1
  have prefixEq : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps := by
    simpa only [programsEq] using codeFacts.2
  exact ⟨sourceCompilerInputs declarations start caller loopCtxt entry limit arch source wc ac stack coracle heapLength
    callerEq loopContextEq codeEq prefixEq ok memory domain shared clock endian ffi current length heap,backend⟩

/-- Lab/source memory agreement on the source domain gives the frontend
memory relation for the actual initialized Stack memory. -/
theorem sourceFullInit_memoryRel {σ : Type}
    (source : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (baseReg : backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word source.baseAddr)
    (sourceDomain : ∀ address, source.memaddrs address ↔
      Flapjack.Compiler.Backend.StackRemove.addresses source.baseAddr
        ((backend.labHeapLength.toNat / 8) + (backend.labHeapLength.toNat / 8)) address)
    (memory : ∀ address, source.memaddrs address →
      backend.lab.memory address = wlabWlocExact (source.memory address)) :
    crepToLoopMemRelHOLExact (concreteDeclCrepState source programs).memory stack.memory
      (concreteDeclCrepState source programs).memaddrs := by
  obtain ⟨base,labBase,heapBase,preserved⟩ := backend.heap_base_and_memory_lab
  have baseEq : base = source.baseAddr := by simpa [baseReg,eq_comm] using labBase
  have current : stack.store.lookup .currHeap = some (.word source.baseAddr) := by simpa [baseEq] using heapBase
  have endHeap := backend.heap_end_lab source.baseAddr current
  intro address member
  have sourceMember : source.memaddrs address := by simpa [concreteDeclCrepState] using member
  have domain := backend.heap_domain_of_pointers source.baseAddr (source.baseAddr + backend.labHeapLength) current endHeap address
  have distance : source.baseAddr + backend.labHeapLength - source.baseAddr = backend.labHeapLength := by simp
  rw [distance] at domain
  have inDomain : stack.mdomain address = true := domain.mpr ((sourceDomain address).mp sourceMember)
  simpa [concreteDeclCrepState] using ((preserved address inDomain).trans (memory address sourceMember)).symm

/-- Build the data fields of a Pancake entry from the Lab input of full
initialization, retaining the template's code and local environments. -/
noncomputable def labInitializedSource {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) : PanSemStateFiniteExact 64 σ :=
  let base := wordSemTheWord (backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2))
  {template with
    memory := fun address => .word (wordSemTheWord (backend.lab.memory address))
    memaddrs := Flapjack.Compiler.Backend.StackRemove.addresses base
      ((backend.labHeapLength.toNat / 8) + (backend.labHeapLength.toNat / 8))
    shMemaddrs := fun address => backend.lab.sharedMemDomain address = true
    clock := backend.lab.clock
    be := backend.lab.be
    ffi := backend.lab.ffi
    baseAddr := base
    topAddr := base + 2 * backend.labHeapLength }

/-- Original source entry whose no-globals call consumes the one clock tick
needed to reach the Lab-aligned pre-call state. -/
noncomputable def labInitializedOriginal {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) : PanSemStateFiniteExact 64 σ :=
  {labInitializedSource template stack backend with clock := backend.lab.clock - 1}

/-- The source-first no-globals call entry has exactly the Lab-aligned data
and the requested compiled source code table. -/
theorem labInitializedOriginal_preCall {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (clockPositive : 0 < backend.lab.clock) :
    noGlobalsLoweredPreCall (labInitializedOriginal template stack backend) code =
      {labInitializedSource template stack backend with code := code} := by
  simp [noGlobalsLoweredPreCall,labInitializedOriginal,labInitializedSource]
  omega

open Classical in
/-- Build the executable source data from the same Lab state as the HOL
source, retaining the production template's code, environments and FFI. -/
noncomputable def labInitializedProduction {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  let source := labInitializedOriginal template stack backend
  {production with
    memory := fun address => some (.word (wordSemTheWord (backend.lab.memory address)))
    memaddrs := fun address => decide (source.memaddrs address)
    sharedMemaddrs := backend.lab.sharedMemDomain
    clock := source.clock
    be := source.be
    baseAddress := source.baseAddr
    topAddress := source.topAddr}

/-- Changing only the proof clock preserves all executable source data. -/
theorem labInitializedProduction_withClock {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) (clock : Nat) :
    labInitializedProduction production template _ (backend.withClock clock) =
      {labInitializedProduction production template stack backend with clock := clock-1} := by
  simp [labInitializedProduction,labInitializedOriginal,labInitializedSource,
    FullInitMachineContext.withClock,FullInitStackContext.labHeapLength]
  funext address
  exact decide_eq_decide.mpr Iff.rfl

/-- A counted execution is unaffected by the proof clock chosen for Lab. -/
theorem labInitializedProduction_counted_withClock {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) (clock fuel : Nat)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (program : Prog (RiscV.Word 64)) :
    let adjusted := labInitializedProduction production template _ (backend.withClock clock)
    let original := labInitializedProduction production template stack backend
    evalPanValueFfiProgSteps context primitive handler adjusted.structs functions
      adjusted.baseAddress adjusted.topAddress panSemBitVec64BytesInWord fuel
      adjusted.locals adjusted.globals adjusted.memory adjusted.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess adjusted)) =
    evalPanValueFfiProgSteps context primitive handler original.structs functions
      original.baseAddress original.topAddress panSemBitVec64BytesInWord fuel
      original.locals original.globals original.memory original.ffi program
      (memoryAccess := some (panSemBitVec64MemoryAccess original)) := by
  rw [labInitializedProduction_withClock]
  rfl

/-- The executable and HOL templates agree on their code and environments. -/
def PanSemEnvironmentRel {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ) : Prop :=
  (∀ name, NameRanged name → Option.map panValueToHOL (production.locals name) = template.locals.lookup (ofString name)) ∧
  (∀ name, NameRanged name → Option.map panValueToHOL (production.globals name) = template.globals.lookup (ofString name)) ∧
  panStructContextToHOL production.structs = template.structs ∧
  (∀ name, NameRanged name → Option.map panLangEntryToHOL (panSemCodeLookup production.code name) = template.code.lookup (ofString name)) ∧
  (∀ name, NameRanged name → Option.map shapeToHOL (production.exceptionShapes name) = template.eshapes.lookup (ofString name))

/-- Updating production data from Lab preserves the source execution bridge;
the template supplies the code/environment relation and the FFI relation. -/
theorem labInitializedProduction_rel {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (templateRel : PanSemEnvironmentRel production template)
    (ffiRel : FfiStateRel production.ffi backend.lab.ffi) :
    PanSemStateRelExec (labInitializedProduction production template stack backend)
      (labInitializedOriginal template stack backend).toExact := by
  classical
  obtain ⟨locals,globals,structs,code,exceptions⟩ := templateRel
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using locals
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using globals
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using structs
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using code
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using exceptions
  · intro address _
    simp [labInitializedProduction,labInitializedOriginal,labInitializedSource,holWordLabBits]
  · intro address
    change decide ((labInitializedOriginal template stack backend).memaddrs address) = true ↔
      (labInitializedOriginal template stack backend).memaddrs address
    exact @decide_eq_true_iff _ _
  · intro address
    simp [labInitializedProduction,labInitializedOriginal,labInitializedSource]
  · rfl
  · rfl
  · simpa [labInitializedProduction,labInitializedOriginal,labInitializedSource] using ffiRel
  · rfl
  · rfl

/-- Lab data updates do not affect the executable representation's ranged
locals, globals or structure context. -/
theorem labInitializedProduction_ranged {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (ranged : PanSemStateRelExecRanged production) :
    PanSemStateRelExecRanged (labInitializedProduction production template stack backend) := by
  simpa [PanSemStateRelExecRanged,labInitializedProduction] using ranged

/-- The canonical source has the heap, register and ambient fields required
by the initializer construction. -/
theorem labInitializedSource_fields {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) :
    let source := labInitializedSource template stack backend
    backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word source.baseAddr ∧
    (∀ address, source.memaddrs address ↔
      Flapjack.Compiler.Backend.StackRemove.addresses source.baseAddr
        ((backend.labHeapLength.toNat / 8) + (backend.labHeapLength.toNat / 8)) address) ∧
    source.topAddr = source.baseAddr + 2 * backend.labHeapLength ∧
    source.clock = backend.lab.clock ∧ source.be = backend.lab.be ∧ source.ffi = backend.lab.ffi ∧
    (∀ address, source.shMemaddrs address ↔ backend.lab.sharedMemDomain address = true) := by
  obtain ⟨base,read,_,_⟩ := backend.heap_base_and_memory_lab
  simp [labInitializedSource,read,wordSemTheWord]

/-- Word-valued Lab memory on the heap yields the required Crep-to-Loop
memory relation for the canonical source, without a condition outside it. -/
theorem labInitializedSource_memoryRel {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (wordMemory : ∀ address, (labInitializedSource template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word) :
    crepToLoopMemRelHOLExact (concreteDeclCrepState (labInitializedSource template stack backend) programs).memory
      stack.memory (concreteDeclCrepState (labInitializedSource template stack backend) programs).memaddrs := by
  have fields := labInitializedSource_fields template stack backend
  apply sourceFullInit_memoryRel (labInitializedSource template stack backend) programs stack backend fields.1 fields.2.1
  intro address inHeap
  obtain ⟨word,read⟩ := wordMemory address inHeap
  simp [labInitializedSource,read,wordSemTheWord,wlabWlocExact]

/-- The Lab-derived source top address is word aligned. -/
theorem labInitializedOriginal_top_aligned {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) :
    panGlobalsByteAlignedHOL (labInitializedOriginal template stack backend).topAddr := by
  have mem := backend.initAssumptions.2.2.2.2.1
  obtain ⟨base,_,_,_,read,_,_,_,_,_,_,_,_,_,baseAligned,_⟩ := mem
  have baseMod : base.toNat % 8 = 0 :=
    (Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm.byteAligned_iff (width := 64) (by simp [goodDimindex]) base).mp baseAligned
  obtain ⟨_,_,length,_,_,lengthStore,_,_,_⟩ := backend.heap_domain
  have lenEq : backend.labHeapLength = BitVec.ofNat 64 length *
      Flapjack.Compiler.Backend.StackRemove.bytesInWord 64 := by
    simpa [backend.heap_length_lab] using lengthStore
  have alignedOfMod (word : BitVec 64) (h : word.toNat % 8 = 0) : panGlobalsByteAlignedHOL word := by
    change BitVec.ofNat 64 ((word.toNat / 8) * 8) = word
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    have hlt := word.isLt
    omega
  apply alignedOfMod
  simp only [labInitializedOriginal,labInitializedSource,read,wordSemTheWord,lenEq]
  simp only [BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,
    Flapjack.Compiler.Backend.StackRemove.bytesInWord]
  have baseLt := base.isLt
  simp only [show (2 : BitVec 64).toNat = 2 by decide]
  norm_num [Flapjack.Compiler.Backend.StackRemove.bytesInWord] at *
  omega

/-- The initialized heap ends before the separately reserved stack area,
so the canonical source top is not an accessible heap word. -/
theorem labInitializedOriginal_top_outside {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) :
    ¬ (labInitializedOriginal template stack backend).memaddrs (labInitializedOriginal template stack backend).topAddr := by
  let bytes := Flapjack.Compiler.Backend.StackRemove.bytesInWord 64
  have good : goodDimindex 64 := by simp [goodDimindex]
  have mem := backend.initAssumptions.2.2.2.2.1
  obtain ⟨p2,p3,p4,_,r2,r3,r4,_,_,_,_,_,_,le,a2,a4,_,big,_⟩ := mem
  have leNat : p2.toNat ≤ p4.toNat := BitVec.le_def.mp le
  have a2Nat : p2.toNat % 8 = 0 := (Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm.byteAligned_iff good p2).mp a2
  have a4Nat : p4.toNat % 8 = 0 := (Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm.byteAligned_iff good p4).mp a4
  have bigNat : 1024 * 8 ≤ p4.toNat - p2.toNat := by
    have h := BitVec.le_def.mp big
    rw [BitVec.toNat_sub_of_le le] at h
    norm_num [Flapjack.Compiler.Backend.StackRemove.bytesInWord] at h ⊢
    exact h
  have maxOk := backend.initAssumptions.2.2.2.2.2.1
  obtain ⟨_,_,heapWords,stackWords,heapEnd,stackEnd,even,_,_,stackMin⟩ :=
    Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm.initLayout good backend.maxHeap maxOk p2 p3 p4 leNat bigNat a2Nat a4Nat
  have limits := Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect.getStackHeapLimit_eq backend.maxHeap p2 p3 p4
  have limitValue : (Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits.getStackHeapLimit backend.maxHeap (p2,p3,p4)).2 = heapWords / 2 := by
    rw [limits]
    simp only [Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimitsDouble.getStackHeapLimitDouble]
    rw [heapEnd]
    omega
  have lenEq : backend.labHeapLength = BitVec.ofNat 64 (heapWords / 2) * bytes := by
    simp only [FullInitStackContext.labHeapLength,r2,r3,r4,wordSemTheWord,limitValue,bytes]
  have halfBound : (heapWords / 2) * 8 < 2^64 := by
    have := p4.isLt
    simp only [Flapjack.Compiler.Backend.StackRemove.maxStackAlloc] at stackMin
    omega
  have totalBound : heapWords * 8 < 2^64 := by
    have := p4.isLt
    simp only [Flapjack.Compiler.Backend.StackRemove.maxStackAlloc] at stackMin
    omega
  have divEven : heapWords / 2 + heapWords / 2 = heapWords := by omega
  intro member
  simp only [labInitializedOriginal,labInitializedSource,r2,wordSemTheWord,lenEq] at member
  have count : (BitVec.ofNat 64 (heapWords / 2) * bytes).toNat / 8 = heapWords / 2 := by
    simp only [BitVec.toNat_mul,BitVec.toNat_ofNat,bytes,Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    have small : heapWords / 2 < 2^64 := by omega
    rw [Nat.mod_eq_of_lt small]
    norm_num at *
    omega
  rw [count,divEven,Flapjack.Compiler.Backend.StackRemove.mem_addresses] at member
  obtain ⟨i,hi,equal⟩ := member
  have eqNat := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,bytes,
    Flapjack.Compiler.Backend.StackRemove.bytesInWord] at eqNat
  have p4Bound := p4.isLt
  have indexBound : i * 8 < 2^64 := by omega
  have halfSmall : heapWords / 2 < 2^64 := by omega
  have indexSmall : i < 2^64 := by omega
  rw [Nat.mod_eq_of_lt halfSmall,Nat.mod_eq_of_lt indexSmall] at eqNat
  simp only [show (2 : BitVec 64).toNat = 2 by decide] at eqNat
  norm_num at *
  omega

/-- Every accessible source heap address is word aligned. -/
theorem labInitializedOriginal_heap_aligned {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) (address : BitVec 64)
    (member : (labInitializedOriginal template stack backend).memaddrs address) :
    holByteAlign address = address := by
  have mem := backend.initAssumptions.2.2.2.2.1
  obtain ⟨base,_,_,_,read,_,_,_,_,_,_,_,_,_,baseAligned,_⟩ := mem
  simp only [labInitializedOriginal,labInitializedSource,read,wordSemTheWord] at member
  rw [Flapjack.Compiler.Backend.StackRemove.mem_addresses] at member
  obtain ⟨i,_,eq⟩ := member
  rw [eq,BitVec.mul_comm]
  have aligned := Flapjack.Compiler.Backend.BackendProof.byteAlignedMult (width := 64)
    (by simp [goodDimindex]) base i
  rw [baseAligned] at aligned
  simpa [holByteAligned,holAligned,holByteAlign,Flapjack.Compiler.Backend.StackRemove.bytesInWord] using aligned

/-- Word-valued aligned Lab memory supplies all source heap cells. -/
theorem labInitializedOriginal_wordMemory {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (alignedWords : ∀ address, ∃ word, backend.lab.memory (holByteAlign address) = .word word) :
    ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word := by
  intro address member
  simpa [labInitializedOriginal_heap_aligned template stack backend address member] using alignedWords address

/-- The standard machine initialization contract supplies the source heap's
word-valued memory when its memory function is the Lab input. -/
theorem labInitializedOriginal_wordMemory_of_goodInit {σ S Q : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (mc : MachineConfig 64 S Q) (ms : S) (bytes : List (BitVec 8)) (cbspace : Nat)
    (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
    (initial : goodInitState mc ms bytes cbspace asm memory dm sdm)
    (memoryEq : backend.lab.memory = memory) :
    ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word := by
  apply labInitializedOriginal_wordMemory template stack backend
  intro address
  obtain ⟨word,read⟩ := goodInitState_wordMemory initial address
  exact ⟨word,by simpa [memoryEq] using read⟩

/-- The counted source theorem's actual no-globals pre-call state has the
required memory relation when Lab heap cells contain words. -/
theorem labInitializedOriginal_preCall_memoryRel {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (clockPositive : 0 < backend.lab.clock)
    (wordMemory : ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word) :
    crepToLoopMemRelHOLExact
      (concreteDeclCrepState (noGlobalsLoweredPreCall (labInitializedOriginal template stack backend) code) programs).memory
      stack.memory
      (concreteDeclCrepState (noGlobalsLoweredPreCall (labInitializedOriginal template stack backend) code) programs).memaddrs := by
  rw [labInitializedOriginal_preCall template stack backend code clockPositive]
  apply labInitializedSource_memoryRel template programs stack backend
  simpa [labInitializedOriginal] using wordMemory

/-- The canonical source's shared domain matches the Lab input. -/
theorem labInitializedSource_shared {σ : Type}
    (template : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (arch : AsmArchitecture)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack) :
    backend.lab.sharedMemDomain = (concreteDeclLoopState arch
      (concreteDeclCrepState (labInitializedSource template stack backend) programs) programs).shMdomain := by
  classical
  funext address
  cases h : backend.lab.sharedMemDomain address <;>
    simp [concreteDeclLoopState,concreteDeclCrepState,labInitializedSource,h]

/-- Construct source inputs for an initializer with a no-install oracle. -/
noncomputable def sourceFullInitEmptyOracleInputs {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (entry : HolLoopProg 64) (limit : Nat) (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (cfg : LabToTarget.Config)
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2)
    (backend : FullInitMachineContext stack)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], []))
    (sourceDomain : ∀ address, source.memaddrs address ↔
      Flapjack.Compiler.Backend.StackRemove.addresses source.baseAddr
        ((backend.labHeapLength.toNat / 8) + (backend.labHeapLength.toNat / 8)) address)
    (shared : backend.lab.sharedMemDomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).shMdomain)
    (clock : backend.lab.clock = source.clock) (endian : backend.lab.be = source.be) (ffi : backend.lab.ffi = source.ffi)
    (baseReg : backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word source.baseAddr)
    (heap : source.topAddr = source.baseAddr + 2 * backend.labHeapLength)
 :
    FullInitAssignLoopInputs declarations start caller loopCtxt entry limit
      {concreteDeclLoopState arch (concreteDeclCrepState source
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := stack.memory} := by
  classical
  have compat := emptyNativeWordOracle_compatible ac backend.bitmaps.length cfg
  have current : stack.store.lookup .currHeap = some (.word source.baseAddr) := by
    obtain ⟨base,labBase,heapBase,_⟩ := backend.heap_base_and_memory_lab
    have baseEq : base = source.baseAddr := by simpa [baseReg,eq_comm] using labBase
    simpa [baseEq] using heapBase
  have domain : stack.mdomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).mdomain := by
    funext address
    have endHeap := backend.heap_end_lab source.baseAddr current
    have domainFact := backend.heap_domain_of_pointers source.baseAddr (source.baseAddr + backend.labHeapLength) current endHeap address
    have distance : source.baseAddr + backend.labHeapLength - source.baseAddr = backend.labHeapLength := by simp
    rw [distance] at domainFact
    have eq := domainFact.trans (sourceDomain address).symm
    cases h : stack.mdomain address <;> by_cases sourceMember : source.memaddrs address <;>
      simp_all [concreteDeclLoopState,concreteDeclCrepState]
  have codeFacts := backend.nativeCompilerCode ac programs inputCodeEq bitmapPrefix
  have ok := backend.nativeInitOk_of_compiled ac programs (emptyNativeWordOracle backend.bitmaps.length cfg)
    registers bitmapPrefix compat.1 (stackOracle.trans compat.2.symm)
  have codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2 := by
    simpa only [programsEq] using codeFacts.1
  have prefixEq : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps := by
    simpa only [programsEq] using codeFacts.2
  let crepPrograms := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let target := {concreteDeclLoopState arch (concreteDeclCrepState source crepPrograms) crepPrograms with memory := stack.memory}
  have data : LoopWordDataRel target
      {callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
        (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
          (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2)
          (emptyNativeWordOracle backend.bitmaps.length cfg))
        with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))} := by
    apply (nativeEntry_loopWordDataRel_iff ac _ 0 stack _ _ _ target).mpr
    refine ⟨backend.labHeapLength,rfl,?_,?_,?_,?_,?_,?_,backend.heap_length_lab,?_,?_⟩
    · simpa [target,crepPrograms] using domain
    · simpa [target,crepPrograms] using backend.ambient_eq.2.2.trans shared
    · simpa [target,concreteDeclLoopState,concreteDeclCrepState] using backend.ambient_eq.1.trans clock
    · simpa [target,concreteDeclLoopState,concreteDeclCrepState] using backend.ambient_eq.2.1.trans endian
    · simpa [target,concreteDeclLoopState,concreteDeclCrepState] using backend.ffi_eq.trans ffi
    · simpa [target,concreteDeclLoopState,concreteDeclCrepState] using current
    · simpa [target,concreteDeclLoopState,concreteDeclCrepState] using heap
    · simp [target,concreteDeclLoopState,loopToWordGlobalsRelHOLExact,HolFiniteMapExact.lookup_empty]
  exact ⟨⟨arch,crepPrograms,rfl,callerEq,loopContextEq,wc,ac,rfl,stack,
    emptyNativeWordOracle backend.bitmaps.length cfg,codeEq,prefixEq,ok,data⟩,backend⟩

/-- Assemble compiler inputs for the canonical Lab-aligned source. -/
noncomputable def labInitializedSource_inputs {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (entry : HolLoopProg 64) (limit : Nat) (arch : AsmArchitecture)
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (cfg : LabToTarget.Config)
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2)
    (backend : FullInitMachineContext stack)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], [])) :
    FullInitAssignLoopInputs declarations start caller loopCtxt entry limit
      {concreteDeclLoopState arch (concreteDeclCrepState (labInitializedSource template stack backend)
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := stack.memory} := by
  have fields := labInitializedSource_fields template stack backend
  exact sourceFullInitEmptyOracleInputs declarations start caller loopCtxt entry limit arch
    (labInitializedSource template stack backend) wc ac stack cfg callerEq loopContextEq programs programsEq
    backend inputCodeEq bitmapPrefix registers stackOracle fields.2.1
    (labInitializedSource_shared template _ arch stack backend)
    fields.2.2.2.1.symm fields.2.2.2.2.1.symm fields.2.2.2.2.2.1.symm fields.1 fields.2.2.1

end SteppedFlapjack.PanToCrepSteps
