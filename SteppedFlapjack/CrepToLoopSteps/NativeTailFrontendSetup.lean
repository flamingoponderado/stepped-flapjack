import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations
import SteppedFlapjack.LoopToWordSteps.NativeTailSetup
import Flapjack.Pancake.LoopToWord.Proofs.LabPres
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas

/-! Join native compiler initialization with the whole frontend code relation. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToWord
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Whole-program compilation constructs a backend setup whose Word state is
related to the actual Loop state, or the native entry reaches a bounded RISC-V
resource outcome. The initial Loop/Stack data relation and the remaining
Stack-to-machine state relations are explicit. -/
theorem wholeNativeTail_frontend_setup_or_resource {F : Type}
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (programShapes : ∀ name params body, (name,params,body) ∈ crepPrograms → SupportedCodeBody body)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (name : Nat)
    (member : (name,1,(LoopToWord.compHOL ctxt p labels).1) ∈
      loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))
    (loop : LoopSemStateFiniteExact 64 F)
    (loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms))
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2)
    (bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
      (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).1.IsPrefix stack.bitmaps)
    (ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac
      (ac.regCount-(5+ac.avoidRegs.length)) stack coracle) (limit : Nat)
    (data : LoopWordDataRel loop
      {callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
        (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
          (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) coracle)
        with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))})
    (backend : NativeTailMachineSetup stack name (tailStackReplayLimit ac 1 name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length))
      (entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) name) p ctxt labels
      (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) limit)) :
    (∃ (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
       (setup : TailRiscVSetup p word limit),
      setup.ctxt = ctxt ∧ setup.machine = backend.machine ∧ setup.mc = backend.mc ∧ setup.lab = backend.lab ∧
      loopToWordStateRelHOLExact loop word ∧
      ∃ (base : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) (frameSize : Nat),
        word.locals = (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) base).locals) ∨
    ∃ ticks finalMachine finalFfi,
      ticks ≤ backend.resourceTickLimit ∧
      evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine =
        (.halt .resourceLimitHit,finalMachine,finalFfi) ∧ finalFfi.ioEvents = stack.ffi.ioEvents := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let originalCode := sptFromAList programs
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
  rcases nativeTail_setup_or_resource wc ac programs p ctxt labels name shapes member nodup stack coracle
      noRaise noStore codeEq bitmapsPrefix ok limit backend with success | resource
  · obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,frameSize,wordEq⟩ := success
    have stackData := (nativeEntry_loopWordDataRel_iff ac k 0 stack compiledCode originalCode coracle loop).mp data
    have frameData := (nativeEntry_loopWordDataRel_iff ac k frameSize stack compiledCode originalCode coracle loop).mpr stackData
    have wordData : LoopWordDataRel loop word := by simpa only [wordEq] using frameData
    obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := wordData
    have wordCode : word.code = originalCode := by simp [wordEq,originalCode]
    have codeRel : loopToWordCodeRelHOLExact loop.code word.code := by
      rw [loopCode,wordCode]
      exact wholeCrepLoopWord_codeRel arch crepPrograms
    refine Or.inl ⟨word,setup,contextEq,machineEq,mcEq,labEq,
      ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals,codeRel⟩,?_⟩
    exact ⟨(Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac k stack compiledCode coracle :
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F), frameSize,by rw [wordEq]⟩
  · exact Or.inr resource

end SteppedFlapjack.CrepToLoopSteps
