import SteppedFlapjack.Concrete.GlobalStructWordOptimized
import SteppedFlapjack.LoopToWordSteps.WordAllocatedSequence
import Flapjack.Compiler.Backend.WordToWord.ExecutableCompile
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordAlloc
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps

def globalStructRegCount : Nat := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)
def globalStructAllocatedProgram : WordLangProgHOL (BitVec 64) :=
  (fullCompileSingleExecutable riscvConfig.twoRegArith globalStructRegCount 3 riscvConfig
    ((65,1,(LoopToWord.compHOL globalStructWordContext globalStructLoopProgram (1,0)).1),none)).2.2

theorem globalStruct_wordAllocated_run :
    LoopBlock globalStructAllocatedProgram ∧ noInstallSubprogsHOL globalStructAllocatedProgram = true ∧
    flatExpConventions globalStructAllocatedProgram = true ∧ postAllocConventionsHOL globalStructRegCount globalStructAllocatedProgram = true ∧
    ∃ loopPost wordPost wordResult selectedLocals targetPost,
      evaluate globalStructLoopProgram {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} =
        (resultToLoop (some (.return [.word 8])),loopPost) ∧
      LoopToWord.CompileCorrect.resultCase globalStructWordContext (.loc 1 0) globalStructWordState
        (resultToLoop (some (.return [.word 8]))) loopPost wordResult wordPost ∧
      wordStateEqRel {wordPost with locals := selectedLocals, clock := globalStructWordLimit-(globalStructWordState.clock-wordPost.clock)} targetPost ∧
      WordSemStateFiniteExact.evaluate globalStructAllocatedProgram
        {globalStructWordState with locals := globalStructWordState.locals, clock := globalStructWordLimit} = (wordResult,targetPost) ∧
      SteppedFlapjack.WordSteps.steps globalStructAllocatedProgram
        {globalStructWordState with locals := globalStructWordState.locals, clock := globalStructWordLimit} ≤
          sizeOf globalStructAllocatedProgram * (globalStructWordLimit+1) := by
  obtain ⟨sourcePost,targetPost,crepPost,loopPost,sourceRun,targetRun,crepRun,loopRun,loopBound⟩ := globalStruct_loop_run
  have shape : LoopSequenceSource globalStructLoopProgram :=
    compile_scalar_optimized_wordShape globalStruct_scalar_program globalStructLoopContext .ln
  have complete : CompleteLoopResult (resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64))) := completeCrep_loop (.return _)
  have noError : resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64)) ≠ some .error := by
    cases complete; simp [resultToLoop]
  have gc : gcFunConstOk globalStructWordState.gcFun := by
    simp [gcFunConstOk,globalStructWordState,concreteDeclWordState,globalStructWordTemplate]
  have localRel : wordLocalsRel (maxVarHOL globalStructWordSimpProgram+1) globalStructWordState.locals globalStructWordState.locals := by
    intro _ _; rfl
  have span := loopSequence_wordAllocated_bound riscvConfig 1 65 3 globalStructRegCount none globalStructLoopProgram shape
    _ loopPost _ globalStructWordState globalStructWordContext (1,0) globalStructWordState.locals globalStructLoopVisitLimit
    ⟨by simpa [globalStructLoopProgram] using loopRun,noError,globalStruct_wordStateRel,globalStruct_initialLocals,
      globalStruct_returnSlot,Or.inr rfl,by decide,globalStruct_wordVars_covered⟩ complete gc
    (by simpa [globalStructWordSimpProgram] using localRel) globalStruct_wordDomain
    (by simpa [globalStructLoopVisitLimit,globalStructLoopProgram] using loopBound)
  rw [← fullCompileSingleExecutable_eq] at span
  obtain ⟨block,noInstall,flat,allocated,wordPost,wordResult,selectedLocals,final,resultRel,ffi,stateRel,run,bound⟩ := span
  refine ⟨?_,?_,?_,?_,loopPost,wordPost,wordResult,selectedLocals,final,?_,resultRel,?_,?_,?_⟩
  · simpa [globalStructAllocatedProgram] using block
  · simpa [globalStructAllocatedProgram] using noInstall
  · simpa [globalStructAllocatedProgram] using flat
  · simpa [globalStructAllocatedProgram] using allocated
  · simpa [globalStructLoopProgram] using loopRun
  · simpa [globalStructWordLimit] using stateRel
  · simpa [globalStructAllocatedProgram,globalStructWordLimit] using run
  · simpa [globalStructAllocatedProgram,globalStructWordLimit] using bound
end SteppedFlapjack.Concrete
