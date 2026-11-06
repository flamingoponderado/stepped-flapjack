import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileBitmaps

/-! Derive native Word-to-Stack initialization from full initialization. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordSimp
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- The standard full-initialization assumptions ensure that the optional
Stack initializer succeeds, even though the machine context stores only the
initialized Stack state. -/
theorem FullInitMachineContext.initializer_succeeds {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack) :
    ∃ initialized,
      (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.bitmaps
        backend.inputCode backend.lab backend.saveRegs backend.dataSp backend.coracle).2 = some initialized := by
  have bundles := And.intro (dischargeThese_s2 backend.initAssumptions) (propagateThese_s2 backend.initAssumptions)
  obtain ⟨initialized,opt,_⟩ := InitSemantics.makeInitSemantics backend.stackConf.jump backend.offset
    (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.sp BvlToBvi.initGlobalsLocation
    (coracle1 backend.coracle) (code1 backend.dataConf backend.inputCode)
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode
      backend.lab backend.saveRegs backend.coracle) backend.bitmaps backend.dataSp bundles
  exact ⟨initialized,by simpa only [fullMakeInit_eq] using opt⟩

/-- Full initialization supplies the native entry-state validity relation
when the native oracle obeys the compiler's conventions and generates the
Stack oracle. The bitmap header and available register count are explicit. -/
theorem FullInitMachineContext.nativeInitOk {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (ac : AsmConfigExact 64)
    (wordOracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (tail : List (BitVec 64))
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmaps : backend.bitmaps = 4 :: tail)
    (oracleValid : ∀ n,
      let ((bm0, _), progs) := wordOracle n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = backend.bitmaps.length))
    (oracleEq : backend.coracle = (fun n =>
      let ((bm0,cfg),progs) := wordOracle n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (cfg,compiled,appListAppend bm.1))) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack wordOracle := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  have fullPair : fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode backend.lab backend.saveRegs backend.dataSp backend.coracle =
        (stack,some initialized) := Prod.ext backend.stackEq.symm fullOpt
  exact Flapjack.Compiler.Backend.StackToLab.Proofs.EncodingInitState.impInitStateOk
    ⟨registers,bitmaps,backend.initAssumptions.1,oracleValid,oracleEq,fullPair⟩


/-- Full initialization installs the supplied Stack code and bitmaps. -/
theorem FullInitMachineContext.stack_code_and_bitmaps {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack) :
    stack.code = sptFromAList backend.inputCode ∧ stack.bitmaps = backend.bitmaps := by
  obtain ⟨initialized,fullOpt⟩ := backend.initializer_succeeds
  have codeEq := congrArg (fun s : StackSemStateFiniteExact 64 LabToTarget.Config F => s.code) backend.stackEq
  have bitmapEq := congrArg (fun s : StackSemStateFiniteExact 64 LabToTarget.Config F => s.bitmaps) backend.stackEq
  constructor
  · rw [codeEq,fullMakeInit_eq]
    rfl
  · rw [bitmapEq,fullMakeInit_eq]
    change (InitMake.makeInitAny (StackToLab.isGenGc backend.dataConf.gcKind) backend.maxHeap backend.bitmaps backend.dataSp
      (coracle1 backend.coracle) backend.stackConf.jump backend.offset backend.sp (sptFromAList (code1 backend.dataConf backend.inputCode))
      (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode backend.lab backend.saveRegs backend.coracle)).bitmaps = backend.bitmaps
    rw [InitAny.makeInitAnyBitmaps]
    simp only [fullMakeInit_eq] at fullOpt
    simp [fullOpt]


/-- The full initializer and an actual native compiler output provide the
Stack code and bitmap-prefix premises used by the source compiler bundle. -/
theorem FullInitMachineContext.nativeCompilerCode {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : backend.inputCode = (compileNative ac false programs).2.2.2)
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps) :
    stack.code = sptFromAList (compileNative ac false programs).2.2.2 ∧
    (compileNative ac false programs).1.IsPrefix stack.bitmaps := by
  obtain ⟨code,bitmaps⟩ := backend.stack_code_and_bitmaps
  exact ⟨by simpa only [codeEq] using code,by simpa only [bitmaps] using bitmapPrefix⟩


/-- A bitmap table extending the actual native compiler output has the
header required by the native initialization proof. -/
theorem FullInitMachineContext.nativeBitmapHeader {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps) :
    ∃ tail, backend.bitmaps = 4 :: tail := by
  rcases compiled : compileNative ac false programs with ⟨bitmaps,config,rest⟩
  have header := (compileWordToStackBitmaps ac programs bitmaps config rest compiled).1
  rw [compiled] at bitmapPrefix
  cases bitmaps with
  | nil => simp at header
  | cons head tail =>
    simp only at header
    subst head
    obtain ⟨suffix,eq⟩ := bitmapPrefix
    exact ⟨tail ++ suffix,by simpa using eq.symm⟩


/-- Native initialization validity follows from the full initializer and
actual bitmap prefix, with only register and oracle compatibility conditions. -/
theorem FullInitMachineContext.nativeInitOk_of_compiled {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (wordOracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (oracleValid : ∀ n,
      let ((bm0, _), progs) := wordOracle n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = backend.bitmaps.length))
    (oracleEq : backend.coracle = (fun n =>
      let ((bm0,cfg),progs) := wordOracle n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (cfg,compiled,appListAppend bm.1))) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack wordOracle := by
  obtain ⟨tail,header⟩ := backend.nativeBitmapHeader ac programs bitmapPrefix
  exact backend.nativeInitOk ac wordOracle tail registers header oracleValid oracleEq


/-- An oracle that never installs code and begins at the supplied bitmap
length. Its configuration is carried through unchanged. -/
def emptyNativeWordOracle (bitmapLength : Nat) (cfg : LabToTarget.Config) :
    Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((bitmapLength,cfg),[])

/-- The empty Word oracle satisfies all compiler conventions and translates
to the empty Stack oracle. -/
theorem emptyNativeWordOracle_compatible (ac : AsmConfigExact 64) (bitmapLength : Nat)
    (cfg : LabToTarget.Config) :
    (∀ n,
      let ((bm0, _), progs) := emptyNativeWordOracle bitmapLength cfg n
      progs.all (fun p => postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) p.2.2) = true ∧
      progs.all (fun p => flatExpConventions p.2.2) = true ∧
      progs.all (fun p => decide (raiseStubLocation ≠ p.1)) = true ∧
      progs.all (fun p => decide (storeConstsStubLocation ≠ p.1)) = true ∧
      (n = 0 → bm0 = bitmapLength)) ∧
    (fun n =>
      let ((bm0,c),progs) := emptyNativeWordOracle bitmapLength cfg n
      let (compiled,_,bm) := compileWordToStackNative ac false (ac.regCount-(5+ac.avoidRegs.length)) progs (.nil,bm0)
      (c,compiled,appListAppend bm.1)) = (fun _ => (cfg,[],[])) := by
  constructor
  · intro n
    simp [emptyNativeWordOracle]
  · funext n
    simp [emptyNativeWordOracle,compileWordToStackNative,appListAppend,appendAux]

/-- For a Stack oracle that never installs code, all Word-oracle convention
and translation obligations follow from the empty oracle construction. -/
theorem FullInitMachineContext.nativeInitOk_emptyOracle {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (bitmapPrefix : (compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (stackOracle : backend.coracle = fun _ => (cfg,[],[])) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack (emptyNativeWordOracle backend.bitmaps.length cfg) := by
  have compat := emptyNativeWordOracle_compatible ac backend.bitmaps.length cfg
  apply backend.nativeInitOk_of_compiled ac programs _ registers bitmapPrefix compat.1
  exact stackOracle.trans compat.2.symm

end SteppedFlapjack.LoopToWordSteps
