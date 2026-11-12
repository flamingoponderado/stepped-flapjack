import SteppedFlapjack.Concrete.GlobalStructWord
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend.WordSimp
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

def globalStructWordLimit : Nat := 6 * globalStructLoopVisitLimit
def globalStructWordSimpProgram : WordLangProgHOL (BitVec 64) :=
  compileExp (LoopToWord.compHOL globalStructWordContext globalStructLoopProgram (1,0)).1

theorem globalStruct_wordSimp_run : ∃ sourcePost targetPost crepPost loopPost wordPost wordResult,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    evalCrepSemHOLProgExact globalStructCrepState globalStructCrepProgram = (some (.return [.word 8]),crepPost) ∧
    evaluate globalStructLoopProgram {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} =
      (resultToLoop (some (.return [.word 8])),loopPost) ∧
    WordSemStateFiniteExact.evaluate globalStructWordSimpProgram {globalStructWordState with clock := globalStructWordLimit} =
      (wordResult,{wordPost with clock := globalStructWordLimit-(globalStructWordState.clock-wordPost.clock)}) ∧
    LoopToWord.CompileCorrect.resultCase globalStructWordContext (.loc 1 0) globalStructWordState
      (resultToLoop (some (.return [.word 8]))) loopPost wordResult wordPost ∧
    SteppedFlapjack.WordSteps.steps globalStructWordSimpProgram {globalStructWordState with clock := globalStructWordLimit} ≤
      sizeOf globalStructWordSimpProgram * (globalStructWordLimit + 1) := by
  obtain ⟨sourcePost,targetPost,crepPost,loopPost,sourceRun,targetRun,crepRun,loopRun,loopBound⟩ := globalStruct_loop_run
  have shape : LoopSequenceSource globalStructLoopProgram :=
    compile_scalar_optimized_wordShape globalStruct_scalar_program globalStructLoopContext .ln
  have complete : CompleteLoopResult (resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64))) :=
    completeCrep_loop (.return _)
  have noError : resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64)) ≠ some .error := by
    cases complete; simp [resultToLoop]
  have gc : gcFunConstOk globalStructWordState.gcFun := by
    simp [gcFunConstOk,globalStructWordState,concreteDeclWordState,globalStructWordTemplate]
  obtain ⟨wordPost,wordResult,wordRun,_,resultRel,wordBound⟩ := loopSequence_wordSimp_bound
    globalStructLoopProgram shape _ loopPost _ globalStructWordState globalStructWordContext (1,0) globalStructLoopVisitLimit
    ⟨by simpa [globalStructLoopProgram] using loopRun,noError,globalStruct_wordStateRel,globalStruct_initialLocals,
      globalStruct_returnSlot,Or.inr rfl,by decide,globalStruct_wordVars_covered⟩
    complete gc (by simpa [globalStructLoopVisitLimit,globalStructLoopProgram] using loopBound)
  exact ⟨sourcePost,targetPost,crepPost,loopPost,wordPost,wordResult,sourceRun,targetRun,crepRun,
    by simpa [globalStructLoopProgram] using loopRun,by simpa [globalStructWordSimpProgram,globalStructWordLimit] using wordRun,
    resultRel,by simpa [globalStructWordSimpProgram,globalStructWordLimit] using wordBound⟩
end SteppedFlapjack.Concrete
