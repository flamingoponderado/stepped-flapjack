import SteppedFlapjack.PanToCrepSteps.CountdownZeroSetupSafe
import SteppedFlapjack.CrepToLoopSteps.FullInitNativeFrontend

/-! Connect the zero-count native setup to the whole Crep frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps

/-- The whole frontend constructs the concrete zero-count stack-safe setup,
with its Loop-to-Word state relation and initial return-location locals. -/
theorem countdownZero_wholeFrontend_safe {F : Type}
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (programShapes : ∀ name params body, (name,params,body) ∈ crepPrograms → SupportedCodeBody body)
    (wc : WordToWord.Config) (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat)
    (member : (firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1) ∈
      loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))
    (loop : LoopSemStateFiniteExact 64 F)
    (loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (WordToStack.Native.compileNative riscvConfig false
      (compile wc riscvConfig (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2)
    (bitmapsPrefix : (WordToStack.Native.compileNative riscvConfig false
      (compile wc riscvConfig (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).1.IsPrefix stack.bitmaps)
    (ok : InitializationStateRel.initStateOk riscvConfig countdownZeroLimit stack coracle) (limit : Nat)
    (data : LoopWordDataRel loop {countdownZeroInitialWord stack coracle with
      code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))})
    (backend : FullInitMachineContext stack) (entryBody : HolProg 64)
    (zeroEntry : sptLookup firstLoopName stack.code = some (.seq (.stackAlloc 0) entryBody))
    (enabled : stack.useStack = true)
    (wordCode : sptFromAList (compile wc riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2 = countdownZeroWordCode) :
    ∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
       (setup : FullInitTailSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      setup.tickLimit = backend.successTickLimit wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) p ctxt labels limit ∧
      loopToWordStateRelHOLExact loop word ∧ setup.wordSafe ∧
      ∃ (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F),
        word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some 0) base).locals := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
  have nodup : (programs.map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  have minimum : ∀ entry ∈ programs, 60 ≤ entry.1 := by
    apply LoopToWord.loop_to_word_compile_lab_min _ _ 60
    exact ⟨rfl,crep_to_loop_compile_prog_lab_min arch _ _ rfl⟩
  have noRaise : raiseStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [raiseStubLocation,wordNumStubs,stackNumStubs] at lower
  have noStore : storeConstsStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [storeConstsStubLocation,wordNumStubs,stackNumStubs] at lower
  have shapes : TailProgramShapes programs := wholeCrep_word_shapes arch crepPrograms programShapes
  obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordEq,safe⟩ :=
    countdownZero_fullInitNativeTail_setup wc programs p ctxt labels shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit backend entryBody zeroEntry enabled wordCode
  have wordData : LoopWordDataRel loop word := by simpa only [wordEq] using data
  obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := wordData
  have originalCode : word.code = sptFromAList programs := by simp [wordEq]
  have codeRel : loopToWordCodeRelHOLExact loop.code word.code := by
    rw [loopCode,originalCode]
    exact wholeCrepLoopWord_codeRel arch crepPrograms
  refine ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,
    ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,codeRel⟩,safe,?_⟩
  exact ⟨WordToStack.Native.Initialization.makeInit riscvConfig countdownZeroLimit stack countdownZeroWordCode coracle,
    by rw [wordEq]; rfl⟩

end SteppedFlapjack.PanToCrepSteps
