import SteppedFlapjack.PanToCrepSteps.SourceNativeInputs
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs
import SteppedFlapjack.LoopToWordSteps.FullInitNativeValidity

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
