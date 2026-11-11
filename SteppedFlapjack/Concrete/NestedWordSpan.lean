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
  have found : (functionsHOL (nestedHOLFunctions.map DeclHOL.function)).lookup (Flapjack.Basis.Pure.MlString.ofString "main") =
      some ([],progToHOL nestedCallEntry,.one) := by
    rw [nestedHOLDeclarations]
    simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]
  have fresh : newMainNameHOL (nestedCallDeclarations.map declToHOL) =
      Flapjack.Basis.Pure.MlString.ofString "main'" := by
    simp [newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,
      Flapjack.Basis.Pure.MlString.ofString,Flapjack.Basis.Pure.MlString.MlString.explode_implode]
  have heap : nestedCrepState.topAddr = nestedCrepState.baseAddr + 2 * fixtureHeapLength := by decide
  have start := functionOnly_optimizedWord nestedHOLFunctions (Flapjack.Basis.Pure.MlString.ofString "main")
    (progToHOL nestedCallEntry) found nestedHOLFunctionShapes
    (by simpa only [nestedHOLDeclarations] using nestedCall_inline_selection_empty)
    riscvConfig.isa {nestedCrepState with clock := clock} template fixtureHeapLength frame wc ac memory limit 7 loopPost
    (by simpa using heap)
    (by simpa only [nestedHOLDeclarations, ← nestedOptimizedLoopBody_eq, nestedOptimizedLoopBody, nestedCrepBody,
      nestedPanContext, nestedLoopContext, nestedCallCrepPrograms, nestedLoopState, concreteDeclLoopState, fresh] using loopRun)
    (by simpa only [nestedHOLDeclarations, ← nestedOptimizedLoopBody_eq, nestedOptimizedLoopBody, nestedCrepBody,
      nestedPanContext, nestedLoopContext, nestedCallCrepPrograms, nestedLoopState, concreteDeclLoopState, fresh] using loopBound)
  simpa only [nestedHOLDeclarations, nestedCallCrepPrograms, firstLoopName] using start

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
