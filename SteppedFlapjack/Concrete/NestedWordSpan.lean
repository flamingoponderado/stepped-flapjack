import SteppedFlapjack.Concrete.NestedLoopRun
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordSimpSteps
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- The actual two-level witness reaches the optimized Word start call with
an explicit visit bound over its compiled table. -/
theorem nested_optimized_start {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat)
    (wc : Config) (ac : AsmConfigExact 64) (memory : BitVec 64 → WordLocW 64)
    (clock limit : Nat) (loopPost : LoopSemStateFiniteExact 64 Unit)
    (loopRun : evaluate nestedLoopCode64 {nestedLoopState with memory := memory,clock := clock} =
      (some (.result [.word 7]),loopPost))
    (loopBound : LoopSteps.steps nestedLoopCode64 {nestedLoopState with memory := memory,clock := clock} ≤ limit) :
    let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let starter := {(phase3Starter riscvConfig.isa {nestedCrepState with clock := clock} nestedCallCrepPrograms template fixtureHeapLength 64 frame)
      with memory := memory}
    let state := {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = loopPost.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac words).2)) * (6*limit+1) := by
  let loop := {nestedLoopState with memory := memory, clock := clock}
  let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
  let words := loopToWordCompileHOL loops
  let starter := {(phase3Starter riscvConfig.isa {nestedCrepState with clock := clock} nestedCallCrepPrograms template fixtureHeapLength 64 frame)
    with memory := memory}
  let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
    (sptDifference (accVarsHOL nestedLoopCode64 .ln) (LoopToWord.toNumSetHOL []))) .ln
  let word := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
    (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
  have heap : nestedCrepState.topAddr = nestedCrepState.baseAddr + 2 * fixtureHeapLength := by decide
  have starterFacts := phase3Starter_relations riscvConfig.isa {nestedCrepState with clock := clock} nestedCallCrepPrograms template fixtureHeapLength 64 frame memory heap
  have localFacts := phase3Starter_locals riscvConfig.isa {nestedCrepState with clock := clock} nestedCallCrepPrograms template fixtureHeapLength 64 frame nestedLoopCode64 memory
  have entryMember : (64,1,(LoopToWord.compHOL ctxt nestedLoopCode64 (64,2)).1) ∈ words := by
    change (64,1,loopToWordCompFuncHOL 64 [] nestedLoopCode64) ∈ words
    simp [words,loops,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have nodup : (words.map Prod.fst).Nodup := by
    simp [words,loops,nestedCall_loop_code,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have table : LoopTableSupported loop.code := by
    change LoopTableSupported (sptFromAList loops)
    exact nestedCall_generated_table_supported
  have shape : SimpleLoopSequenceSource nestedLoopCode64 := by
    apply table 64 [] nestedLoopCode64
    simp [loop,nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,sptLookup_sptFromAList,sptAListLookup]
  have premises :
    let w := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
      (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
    evaluate nestedLoopCode64 loop = (some (.result [.word 7]),loopPost) ∧
    (some (.result [.word 7]) : Option (LoopResultExact 64)) ≠ some .error ∧
    loopToWordStateRelHOLExact loop w ∧ LoopToWord.localsRelHOL ctxt loop.locals w.locals ∧
    sptLookup 0 w.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
    (∀ k, sptMem k (accVarsHOL nestedLoopCode64 .ln) → sptMem k ctxt) := by
    refine ⟨loopRun,by simp,?_,?_,localFacts.2.1,?_,by decide,localFacts.2.2⟩
    · simpa [loop,nestedLoopState,starter,concreteDeclLoopState] using starterFacts.1
    · simpa [loop,nestedLoopState,starter,concreteDeclLoopState] using localFacts.1
    · exact Or.inr rfl
  have span := loopTable_wholeWord_span shape loop loopPost
    (some (.result [.word 7])) table 64 starter ctxt (64,2) limit words wc ac entryMember nodup
    (loopToWord_programSafety loops) rfl starterFacts.2.1 starterFacts.2.2.1 starterFacts.2.2.2
    premises (.return [.word 7]) loopBound
  obtain ⟨wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  let state := {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2}
  refine ⟨(WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state).2,?_,?_,?_⟩
  · exact Prod.ext (by simpa [state,relation.2.1] using result) rfl
  · exact ffi
  · simpa [state,starter,words,loops] using bound
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- The counted source bound reaches the compiled Word start call. -/
theorem nestedCounted_word_start {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat)
    (wc : Config) (ac : AsmConfigExact 64) (memory : BitVec 64 → WordLocW 64) :
    let words := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
    let starter := phase3Starter riscvConfig.isa
      {nestedCrepState with clock := nestedLoopState.clock+nestedLoopBudget}
      nestedCallCrepPrograms template fixtureHeapLength 64 frame
    let state := {starter with memory := memory, clock := 6*nestedOptimizedLoopBound+1, code := sptFromAList (compile wc ac words).2}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = sourceFfi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable wc ac words).2)) *
          (6*nestedOptimizedLoopBound+1) := by
  obtain ⟨loopFinal,run,ffi,bound⟩ := nestedCounted_optimizedLoop memory
  have span := nested_optimized_start template frame wc ac memory
    (nestedLoopState.clock+nestedLoopBudget) nestedOptimizedLoopBound loopFinal
    (by simpa using run) (by simpa using bound)
  simpa [ffi] using span

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
/-- The nested witness also executes from the native initialized Word state. -/
theorem nested_configured_optimized_start (code : List (Nat × StackLang.HolProg 64))
    (cfg : LabToTarget.Config) (bs : List (BitVec 64))
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame : Nat)
    (frameLookup : let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
      let words := (compile phase3WordConfig riscvConfig (loopToWordCompileHOL loops)).2
      sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame) :
    let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
    let rawWords := loopToWordCompileHOL loops
    let words := (compile phase3WordConfig riscvConfig rawWords).2
    let state := {(configuredWord code words cfg bs) with clock := 6*nestedOptimizedLoopBound+1}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = sourceFfi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig rawWords).2)) * (6*nestedOptimizedLoopBound+1) := by
  let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
  let rawWords := loopToWordCompileHOL loops
  let words := (compile phase3WordConfig riscvConfig rawWords).2
  let template := configuredWord code words cfg bs
  let mem := (configuredStack code cfg bs).memory
  have span := nestedCounted_word_start template frame phase3WordConfig riscvConfig mem
  have start := configuredStarter .skip 3 0 (.skip : ProgHOL 64) nestedCallCrepPrograms
    code words cfg bs fits good frame (6*nestedOptimizedLoopBound+1) frameLookup
  have codeEq : template.code = sptFromAList words := by
    simp [template,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit]
  have eq : {(phase3Starter riscvConfig.isa {nestedCrepState with clock := nestedLoopState.clock+nestedLoopBudget} nestedCallCrepPrograms template fixtureHeapLength 64 frame) with
      memory := (configuredStack code cfg bs).memory, clock := 6*nestedOptimizedLoopBound+1,
      code := sptFromAList words} = {template with clock := 6*nestedOptimizedLoopBound+1} := by
    rw [← codeEq]
    convert start using 1
    all_goals simp [template,words,rawWords,loops,phase3Starter,concreteDeclWordState,concreteDeclLoopState,
      nestedCrepState,crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
      panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate]
    constructor <;> funext a <;> apply Bool.eq_iff_iff.mpr <;> exact Iff.rfl
  dsimp only [mem] at span
  change (∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
    {(phase3Starter riscvConfig.isa {nestedCrepState with clock := nestedLoopState.clock+nestedLoopBudget} nestedCallCrepPrograms template fixtureHeapLength 64 frame) with
      memory := (configuredStack code cfg bs).memory, clock := 6*nestedOptimizedLoopBound+1,code := sptFromAList words} =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = sourceFfi ∧ _ ) at span
  rw [eq] at span
  simpa [template,words,rawWords,loops] using span

end SteppedFlapjack.Concrete
