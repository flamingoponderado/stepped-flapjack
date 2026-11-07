import SteppedFlapjack.PanToCrepSteps.CountdownZeroStackMax
import SteppedFlapjack.LoopToWordSteps.FullInitTailSafe
import SteppedFlapjack.LoopToWordSteps.FullInitNativeZeroFrame

/-! Connect the concrete Word stack bound to a full-initializer setup. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

/-- The actual optimized zero-count code and initialized Word state make a
full-initializer setup stack-safe, for any source replay limit. -/
theorem countdownZero_setup_wordSafe {F : Type} {p : HolLoopProg 64} {limit : Nat}
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (backend : FullInitMachineContext stack)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (setup : FullInitTailSetup p word limit)
    (originalCode : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (wordEq : word = {countdownZeroInitialWord stack coracle with code := originalCode})
    (codeEq : setup.compiledCode = countdownZeroWordCode)
    (entryLookup : sptLookup 64 setup.compiledCode = some (1,
      (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
        ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2)) :
    setup.wordSafe := by
  have entryEq : (fullCompileSingle setup.ac.twoRegArith setup.regCount setup.alg setup.ac
      ((setup.name,setup.count,(LoopToWord.compHOL setup.ctxt p setup.labels).1),setup.col)).2.2 =
      countdownZeroOptimizedEntry := by
    rw [codeEq,countdownZeroOptimizedEntry_lookup] at entryLookup
    exact (Prod.mk.inj (Option.some.inj entryLookup)).2.symm
  have safe := countdownZero_fullInit_entry_resource_safe stack backend coracle setup.locals
    (tailWordReplayLimit p setup.ctxt setup.labels setup.compiledCode limit)
  have initialCode : (countdownZeroInitialWord stack coracle).code = countdownZeroWordCode := rfl
  unfold FullInitTailSetup.wordSafe
  dsimp only
  simpa only [entryEq,wordEq,codeEq,initialCode] using safe

/-- A zero-frame native setup using the concrete countdown Word code is
constructed with the stack-safety property required by the RISC-V proof. -/
theorem countdownZero_fullInitNativeTail_setup {F : Type}
    (wc : WordToWord.Config) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (shapes : TailProgramShapes programs)
    (member : (firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : stack.code = sptFromAList (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile wc riscvConfig programs).2).2.2.2)
    (bitmapsPrefix : (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile wc riscvConfig programs).2).1.IsPrefix stack.bitmaps)
    (ok : WordToStackProofs.InitializationStateRel.initStateOk riscvConfig countdownZeroLimit stack coracle)
    (limit : Nat) (backend : FullInitMachineContext stack)
    (entryBody : Flapjack.Compiler.Backend.StackLang.HolProg 64)
    (zeroEntry : sptLookup firstLoopName stack.code = some (.seq (.stackAlloc 0) entryBody))
    (enabled : stack.useStack = true)
    (wordCode : sptFromAList (WordToWord.compile wc riscvConfig programs).2 = countdownZeroWordCode) :
    ∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
      (setup : FullInitTailSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      setup.tickLimit = backend.successTickLimit wc riscvConfig programs p ctxt labels limit ∧
      word = {countdownZeroInitialWord stack coracle with code := sptFromAList programs} ∧ setup.wordSafe := by
  have enoughRegs : 1 ≤ riscvConfig.regCount-(5+riscvConfig.avoidRegs.length) := by decide
  obtain ⟨word,setup,ctxtEq,machineEq,mcEq,labEq,tickEq,frameSize,wordEq,_,_,_,_,_,_,_,compiledEq,_,_,frameZero,entryLookup⟩ :=
    fullInitNativeTail_zeroFrame_setup wc riscvConfig programs p ctxt labels shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit backend entryBody zeroEntry enabled enoughRegs
  have initialized : word = {countdownZeroInitialWord stack coracle with code := sptFromAList programs} := by
    rw [wordEq,frameZero,wordCode]
    rfl
  have compiled : setup.compiledCode = countdownZeroWordCode := compiledEq.trans wordCode
  have safe := countdownZero_setup_wordSafe stack backend coracle word setup (sptFromAList programs)
    initialized compiled entryLookup
  exact ⟨word,setup,ctxtEq,machineEq,mcEq,labEq,tickEq,initialized,safe⟩

end SteppedFlapjack.PanToCrepSteps
