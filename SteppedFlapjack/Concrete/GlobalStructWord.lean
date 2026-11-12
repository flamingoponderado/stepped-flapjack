import SteppedFlapjack.Concrete.GlobalStructLoop
import SteppedFlapjack.LoopToWordSteps.WordSimpSequenceBound
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopToWord
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

def globalStructLoopProgram : HolLoopProg 64 := optimiseHOL (compileHOLExact globalStructLoopContext .ln globalStructCrepProgram)
def globalStructWordNames : List Nat := (sptToAList (accVarsHOL globalStructLoopProgram .ln)).map Prod.fst

def globalStructWordContext : Spt Nat := makeCtxtHOL 2 globalStructWordNames .ln

theorem globalStruct_wordLocals : LoopToWord.localsRelHOL globalStructWordContext (.ln : Spt (WordLocW 64))
    (sptInsert 0 (.loc 1 0) .ln) := by
  exact LoopToWord.localsRelHOLMkCtxtLn 2 globalStructWordNames _ (by decide)

theorem globalStruct_wordVars_covered : ∀ k, sptMem k (accVarsHOL globalStructLoopProgram .ln) → sptMem k globalStructWordContext := by
  intro k h
  obtain ⟨value,found⟩ := (sptMem_iff_lookup k (accVarsHOL globalStructLoopProgram .ln)).mp h
  have member : k ∈ globalStructWordNames := by
    apply List.mem_map.mpr
    exact ⟨(k,value),(sptMemToAList _ _ _).mpr found,rfl⟩
  change sptDomain (makeCtxtHOL 2 globalStructWordNames .ln) k
  rw [sptDomain_makeCtxtHOL]
  exact Or.inr member


def globalStructWordTemplate : WordSemStateFiniteExact 64 Unit Unit where
  locals := sptInsert 0 (.loc 1 0) .ln
  localsSize := none
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := none
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ i => i
  compile := fun _ _ => none
  compileOracle := fun _ => ((),[])
  codeBuffer := {position := 0, buffer := [], spaceLeft := 0}
  dataBuffer := {position := 0, buffer := [], spaceLeft := 0}
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 0
  code := .ln
  be := false
  ffi := sourceFfi

def globalStructClockedCrep : CrepSemHOLState 64 Unit :=
  {globalStructCrepState with clock := globalStructCrepState.clock + globalStructLoopClock}

noncomputable def globalStructWordState : WordSemStateFiniteExact 64 Unit Unit :=
  concreteDeclWordState riscvConfig.isa globalStructClockedCrep [] globalStructWordTemplate fixtureHeapLength

theorem globalStruct_heapEquation : globalStructClockedCrep.topAddr =
    globalStructClockedCrep.baseAddr + 2 * fixtureHeapLength := by
  change heapTop = heapBase + 2 * fixtureHeapLength
  decide

theorem globalStruct_wordData : LoopWordDataRel
    {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} globalStructWordState := by
  have data := (concreteDecl_word_data riscvConfig.isa globalStructClockedCrep []
    globalStructWordTemplate fixtureHeapLength globalStruct_heapEquation).1
  change LoopWordDataRel (concreteDeclLoopState riscvConfig.isa globalStructClockedCrep [])
    (concreteDeclWordState riscvConfig.isa globalStructClockedCrep [] globalStructWordTemplate fixtureHeapLength)
  exact data


theorem globalStruct_wordStateRel : loopToWordStateRelHOLExact
    {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} globalStructWordState := by
  obtain ⟨len,mem,domain,shared,clock,be,ffi,current,length,heap,globals⟩ := globalStruct_wordData
  refine ⟨len,mem,domain,shared,clock,be,ffi,current,length,heap,globals,?_⟩
  simp [loopToWordCodeRelHOLExact,globalStructLoopState,concreteDeclLoopState,compileProgHOLExact,sptFromAList]

def globalStructLoopVisitLimit : Nat := loopVisitWeight globalStructLoopProgram * (globalStructCrepLimit + globalStructLoopClock + 1)

theorem globalStruct_initialLocals : LoopToWord.localsRelHOL globalStructWordContext
    ({globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock}).locals globalStructWordState.locals := by
  simpa [globalStructLoopState,concreteDeclLoopState,globalStructWordState,concreteDeclWordState,globalStructWordTemplate]
    using globalStruct_wordLocals

theorem globalStruct_returnSlot : sptLookup 0 globalStructWordState.locals = some (.loc 1 0) := by
  simp [globalStructWordState,concreteDeclWordState,globalStructWordTemplate,sptLookup]

theorem globalStruct_word_run : ∃ sourcePost targetPost crepPost loopPost wordPost wordResult,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    evalCrepSemHOLProgExact globalStructCrepState globalStructCrepProgram = (some (.return [.word 8]),crepPost) ∧
    evaluate globalStructLoopProgram {globalStructLoopState with clock := globalStructLoopState.clock + globalStructLoopClock} =
      (resultToLoop (some (.return [.word 8])),loopPost) ∧
    WordSemStateFiniteExact.evaluate (LoopToWord.compHOL globalStructWordContext globalStructLoopProgram (1,0)).1 globalStructWordState =
      (wordResult,wordPost) ∧
    LoopToWord.CompileCorrect.resultCase globalStructWordContext (.loc 1 0) globalStructWordState
      (resultToLoop (some (.return [.word 8]))) loopPost wordResult wordPost ∧
    SteppedFlapjack.WordSteps.steps (LoopToWord.compHOL globalStructWordContext globalStructLoopProgram (1,0)).1 globalStructWordState ≤
      6 * globalStructLoopVisitLimit := by
  obtain ⟨sourcePost,targetPost,crepPost,loopPost,sourceRun,targetRun,crepRun,loopRun,loopBound⟩ := globalStruct_loop_run
  have shape : LoopSequenceSource globalStructLoopProgram :=
    compile_scalar_optimized_wordShape globalStruct_scalar_program globalStructLoopContext .ln
  have complete : CompleteLoopResult (resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64))) :=
    completeCrep_loop (.return _)
  have noError : resultToLoop (some (.return [.word 8] : CrepResultHOLExact 64)) ≠ some .error := by
    cases complete; simp [resultToLoop]
  have localRel := globalStruct_initialLocals
  have returnSlot := globalStruct_returnSlot
  obtain ⟨wordPost,wordResult,wordRun,_,resultRel,_,_,wordBound⟩ := loopSequence_word_execution
    globalStructLoopProgram shape _ loopPost _ globalStructWordState globalStructWordContext (1,0) globalStructLoopVisitLimit
    ⟨by simpa [globalStructLoopProgram] using loopRun,noError,globalStruct_wordStateRel,localRel,returnSlot,Or.inr rfl,by decide,globalStruct_wordVars_covered⟩
    complete (by simpa [globalStructLoopVisitLimit,globalStructLoopProgram] using loopBound)
  exact ⟨sourcePost,targetPost,crepPost,loopPost,wordPost,wordResult,sourceRun,targetRun,crepRun,
    by simpa [globalStructLoopProgram] using loopRun,wordRun,resultRel,wordBound⟩
end SteppedFlapjack.Concrete
