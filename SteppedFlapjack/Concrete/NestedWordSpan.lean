import SteppedFlapjack.Concrete.NestedLoopRun
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordSimpSteps
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- The actual two-level witness reaches the optimized Word start call with
an explicit visit bound over its compiled table. -/
theorem nested_optimized_start {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat)
    (wc : Config) (ac : AsmConfigExact 64) :
    let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let starter := {(phase3Starter riscvConfig.isa nestedCrepState nestedCallCrepPrograms template fixtureHeapLength 64 frame)
      with memory := nestedLoopState.memory}
    let state := {starter with clock := 6*122+1, code := sptFromAList (compile wc ac words).2}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = sourceFfi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac words).2)) * (6*122+1) := by
  let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
  let words := loopToWordCompileHOL loops
  let starter := {(phase3Starter riscvConfig.isa nestedCrepState nestedCallCrepPrograms template fixtureHeapLength 64 frame)
    with memory := nestedLoopState.memory}
  let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
    (sptDifference (accVarsHOL nestedLoopCode64 .ln) (LoopToWord.toNumSetHOL []))) .ln
  let word := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
    (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
  have heap : nestedCrepState.topAddr = nestedCrepState.baseAddr + 2 * fixtureHeapLength := by decide
  have starterFacts := phase3Starter_relations riscvConfig.isa nestedCrepState nestedCallCrepPrograms template fixtureHeapLength 64 frame nestedLoopState.memory heap
  have localFacts := phase3Starter_locals riscvConfig.isa nestedCrepState nestedCallCrepPrograms template fixtureHeapLength 64 frame nestedLoopCode64 nestedLoopState.memory
  have entryMember : (64,1,(LoopToWord.compHOL ctxt nestedLoopCode64 (64,2)).1) ∈ words := by
    change (64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64) ∈ words
    simp [words,loops,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have nodup : (words.map Prod.fst).Nodup := by
    simp [words,loops,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have table : LoopTableSupported nestedLoopState.code := by
    change LoopTableSupported (sptFromAList loops)
    exact nestedCall_generated_table_supported
  have shape : SimpleLoopSequenceSource nestedLoopCode64 := by
    apply table 64 [] nestedLoopCode64
    simp [nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,sptLookup_sptFromAList,sptAListLookup]
  have premises :
    let w := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
      (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
    evaluate nestedLoopCode64 nestedLoopState = (some (.result [.word 7]),{nestedLoopState with locals := .ln,clock := 0}) ∧
    (some (.result [.word 7]) : Option (LoopResultExact 64)) ≠ some .error ∧
    loopToWordStateRelHOLExact nestedLoopState w ∧ LoopToWord.localsRelHOL ctxt nestedLoopState.locals w.locals ∧
    sptLookup 0 w.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
    (∀ k, sptMem k (accVarsHOL nestedLoopCode64 .ln) → sptMem k ctxt) := by
    refine ⟨nestedCall_loop_run,by simp,?_,?_,localFacts.2.1,?_,by decide,localFacts.2.2⟩
    · simpa [nestedLoopState,starter] using starterFacts.1
    · simpa [nestedLoopState,starter] using localFacts.1
    · exact Or.inr rfl
  have span := loopTable_wholeWord_span shape nestedLoopState {nestedLoopState with locals := .ln,clock := 0}
    (some (.result [.word 7])) table 64 starter ctxt (64,2) 122 words wc ac entryMember nodup
    (loopToWord_programSafety loops) rfl starterFacts.2.1 starterFacts.2.2.1 starterFacts.2.2.2
    premises (.return [.word 7]) nestedCall_loop_steps_bound
  obtain ⟨wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  let state := {starter with clock := 6*122+1, code := sptFromAList (compile wc ac words).2}
  refine ⟨(WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state).2,?_,?_,?_⟩
  · exact Prod.ext (by simpa [state,relation.2.1] using result) rfl
  · simpa [state,nestedLoopState,nestedCrepState,concreteDeclLoopState,concreteDeclCrepState,sourceTemplate] using ffi
  · simpa [state,starter,words,loops] using bound
end SteppedFlapjack.Concrete
