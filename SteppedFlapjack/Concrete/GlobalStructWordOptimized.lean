import SteppedFlapjack.Concrete.GlobalStructWordSimp
import SteppedFlapjack.LoopToWordSteps.WordOptimizedSequence
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties
import Flapjack.Misc.Sptree.FromList2
import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordInst Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordCse Flapjack.Compiler.Backend.WordCopy Flapjack.Compiler.Backend.WordUnreach
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

theorem globalStruct_wordVarsBound : everyVarHOL (fun x => decide (x < maxVarHOL globalStructWordSimpProgram + 1)) globalStructWordSimpProgram = true :=
  everyVarMono _ globalStructWordSimpProgram _ ⟨fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega,
    Flapjack.Compiler.Backend.WordAlloc.maxVarMax globalStructWordSimpProgram⟩

theorem globalStruct_wordDomain : sptDomain globalStructWordState.locals = (fun key => key ∈ evenList 1) := by
  change sptDomain (sptInsert 0 (.loc 1 0 : WordLocW 64) .ln) = _
  simpa [sptFromList2,evenList] using (sptDomainFromList2 [(.loc 1 0 : WordLocW 64)])

def globalStructWordOptimizedProgram : WordLangProgHOL (BitVec 64) :=
  removeDeadProg (removeUnreach (threeToTwoRegProg riscvConfig.twoRegArith
    (copyProp (wordCommonSubexpElim (removeDeadProg (fullSsaCcTrans 1
      (instSelectExecutable riscvConfig (maxVarHOL globalStructWordSimpProgram+1) globalStructWordSimpProgram)))))))

theorem globalStruct_wordOptimized_run : ∃ loopPost wordPost wordResult selectedLocals targetPost deadLocals,
    evaluate globalStructLoopProgram {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} =
      (resultToLoop (some (.return [.word 8])),loopPost) ∧
    LoopToWord.CompileCorrect.resultCase globalStructWordContext (.loc 1 0) globalStructWordState
      (resultToLoop (some (.return [.word 8]))) loopPost wordResult wordPost ∧
    WordSemStateFiniteExact.evaluate globalStructWordOptimizedProgram
      {globalStructWordState with locals := globalStructWordState.locals, clock := globalStructWordLimit} =
        (wordResult,{targetPost with locals := deadLocals}) ∧
    Flapjack.WordAlloc.wordStateEqRel {wordPost with locals := selectedLocals, clock := globalStructWordLimit-(globalStructWordState.clock-wordPost.clock)} targetPost ∧
    SteppedFlapjack.WordSteps.steps globalStructWordOptimizedProgram
      {globalStructWordState with locals := globalStructWordState.locals, clock := globalStructWordLimit} ≤
        sizeOf globalStructWordOptimizedProgram * (globalStructWordLimit+1) := by
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
  obtain ⟨wordPost,wordResult,selectedLocals,targetPost',deadLocals,resultRel,_,stateRel,run,bound⟩ :=
    loopSequence_wordOptimized_bound riscvConfig 1 globalStructLoopProgram shape _ loopPost _ globalStructWordState
      globalStructWordContext (1,0) globalStructWordState.locals globalStructLoopVisitLimit
      ⟨by simpa [globalStructLoopProgram] using loopRun,noError,globalStruct_wordStateRel,globalStruct_initialLocals,
        globalStruct_returnSlot,Or.inr rfl,by decide,globalStruct_wordVars_covered⟩ complete gc
      (by simpa [globalStructWordSimpProgram] using globalStruct_wordVarsBound)
      (by simpa [globalStructWordSimpProgram] using localRel) globalStruct_wordDomain
      (by simpa [globalStructLoopVisitLimit,globalStructLoopProgram] using loopBound)
  refine ⟨loopPost,wordPost,wordResult,selectedLocals,targetPost',deadLocals,?_,resultRel,?_,?_,?_⟩
  · simpa [globalStructLoopProgram] using loopRun
  · simpa [globalStructWordOptimizedProgram,instSelectExecutable_eq,globalStructWordSimpProgram,globalStructWordLimit] using run
  · simpa [globalStructWordLimit] using stateRel
  · simpa [globalStructWordOptimizedProgram,instSelectExecutable_eq,globalStructWordSimpProgram,globalStructWordLimit] using bound
end SteppedFlapjack.Concrete
