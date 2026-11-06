import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopNative
import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals

/-! Construct the native frontend input from source and Stack entry data. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Construct the common compiler inputs independently of the backend route. -/
noncomputable def sourceCompilerInputs {σ : Type}
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
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle)
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
    AssignLoopCompilerInputs declarations start caller loopCtxt entry limit
      (concreteDeclLoopState arch (concreteDeclCrepState source
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
  let programs := compileProgDeclsHOLW (compileTopExactHOL declarations start)
  let crep := concreteDeclCrepState source programs
  let compiled := sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch programs))).2
  have data := (concreteDecl_native_word_compatible arch ac (ac.regCount-(5+ac.avoidRegs.length)) 0 stack
    compiled coracle crep programs heapLength memory domain shared
    (by simpa [crep,concreteDeclCrepState] using clock)
    (by simpa [crep,concreteDeclCrepState] using endian)
    (by simpa [crep,concreteDeclCrepState] using ffi)
    (by simpa [crep,concreteDeclCrepState] using current) length
    (by simpa [crep,concreteDeclCrepState] using heap)).1
  exact ⟨arch,programs,rfl,callerEq,loopContextEq,wc,ac,rfl,stack,coracle,codeEq,bitmapsPrefix,ok,data⟩


/-- Construct the whole-compiler native inputs for the source-first Loop
entry. The remaining Stack premises describe actual compiled code, native
initialization and equality of source memory and heap data; `backend` is the
remaining Stack-to-machine setup. -/
noncomputable def sourceNativeInputs {σ : Type}
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
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle)
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
    (backend : NativeTailMachineSetup stack firstLoopName (tailStackReplayLimit ac 1 firstLoopName wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) (entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))) firstLoopName)
      entry (assignLoopEntryWordContext entry) (firstLoopName,2)
      (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))))).2) limit)) :
    AssignLoopNativeInputs declarations start caller loopCtxt entry limit
      (concreteDeclLoopState arch (concreteDeclCrepState source
        (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
        (compileProgDeclsHOLW (compileTopExactHOL declarations start))) := by
  exact ⟨sourceCompilerInputs declarations start caller loopCtxt entry limit arch source wc ac stack coracle heapLength
    callerEq loopContextEq codeEq bitmapsPrefix ok memory domain shared clock endian ffi current length heap,backend⟩


end SteppedFlapjack.PanToCrepSteps
