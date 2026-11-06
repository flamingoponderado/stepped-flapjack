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

/-- Construct source inputs for an initializer with a no-install oracle. -/
noncomputable def sourceFullInitEmptyOracleInputs {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (entry : HolLoopProg 64) (limit : Nat) (arch : AsmArchitecture)
    (source : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (cfg : LabToTarget.Config)
    (heapEnd : BitVec 64)
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
    (memory : stack.memory = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).memory)
    (domain : stack.mdomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).mdomain)
    (shared : backend.lab.sharedMemDomain = (concreteDeclLoopState arch (concreteDeclCrepState source
      (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
      (compileProgDeclsHOLW (compileTopExactHOL declarations start))).shMdomain)
    (clock : backend.lab.clock = source.clock) (endian : backend.lab.be = source.be) (ffi : backend.lab.ffi = source.ffi)
    (baseReg : backend.lab.regs (StackNames.findNameSpt backend.stackConf.regNames 2) = .word source.baseAddr)
    (endHeap : stack.store.lookup .endOfHeap = some (.word heapEnd))
    (heap : source.topAddr = source.baseAddr + 2 * (heapEnd - source.baseAddr))
 :
    FullInitAssignLoopInputs declarations start caller loopCtxt entry limit
      (concreteDeclLoopState arch (concreteDeclCrepState source
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
  have compat := emptyNativeWordOracle_compatible ac backend.bitmaps.length cfg
  have current : stack.store.lookup .currHeap = some (.word source.baseAddr) := by
    obtain ⟨base,labBase,heapBase⟩ := backend.heap_base_lab
    have baseEq : base = source.baseAddr := by simpa [baseReg,eq_comm] using labBase
    simpa [baseEq] using heapBase
  exact sourceFullInitInputs declarations start caller loopCtxt entry limit arch source wc ac stack
    (emptyNativeWordOracle backend.bitmaps.length cfg) (heapEnd - source.baseAddr) callerEq loopContextEq programs programsEq
    backend inputCodeEq bitmapPrefix registers compat.1 (stackOracle.trans compat.2.symm)
    memory domain (backend.ambient_eq.2.2.trans shared) (backend.ambient_eq.1.trans clock)
    (backend.ambient_eq.2.1.trans endian) (backend.ffi_eq.trans ffi) current
    (backend.heap_length_of_pointers source.baseAddr heapEnd current endHeap) heap

end SteppedFlapjack.PanToCrepSteps
