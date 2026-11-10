import SteppedFlapjack.Concrete.WordStarter
import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
variable {C F : Type}
/-- The start-call bound computed from the actual optimized two-function output. -/
noncomputable def twoProgramWordBoundSpec (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (limit : Nat) (wc : Config) (ac : AsmConfigExact 64) : Nat :=
  let words := loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let entryOut := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),entryColour wc words 64)).2.2
  let calleeOut := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)),entryColour wc words 65)).2.2
  1 + wordControlWeight entryOut * (wordControlWeight calleeOut+1) * (6*limit+2)

/-- A computable bound for the actual optimized two-function output. -/
def twoProgramWordBound (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (limit : Nat) (wc : Config) (ac : AsmConfigExact 64) : Nat :=
  let words := loopToWordCompileHOL (twoLoopPrograms arch name callee body)
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let entryOut := (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable ac.twoRegArith k wc.regAlg ac
    ((64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),entryColour wc words 64)).2.2
  let calleeOut := (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable ac.twoRegArith k wc.regAlg ac
    ((65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)),entryColour wc words 65)).2.2
  1 + wordControlWeight entryOut * (wordControlWeight calleeOut+1) * (6*limit+2)

theorem twoProgramWordBound_eq (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (shape : ScalarProgram body) (limit : Nat) (wc : Config) (ac : AsmConfigExact 64) :
    twoProgramWordBound arch name callee body limit wc ac = twoProgramWordBoundSpec arch name callee body limit wc ac := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  unfold twoProgramWordBound twoProgramWordBoundSpec
  rw [← twoLoopPrograms_eq arch name callee body shape, allocator]
  simp only [← fullCompileSingleExecutable_eq]
  rfl


/-- A returning two-function scalar Loop run yields the actual optimized Word
start run with no additional state or code assumptions. -/
theorem twoProgram_wholeWord_span (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64)
    (fresh : name ≠ callee) (shape : ScalarProgram body) (source : CrepSemHOLState 64 F)
    (post : LoopSemStateFiniteExact 64 F) (values : List (WordLocW 64)) (limit : Nat)
    (template : WordSemStateFiniteExact 64 C F) (heapLength : BitVec 64) (frame : Nat)
    (wc : Config) (ac : AsmConfigExact 64) (memory : BitVec 64 → WordLocW 64)
    (heap : source.topAddr = source.baseAddr + 2 * heapLength)
    (run : evaluate branchingLoopEntry ({(concreteDeclLoopState arch source (twoPrograms name callee body)) with memory := memory}) =
      (some (.result values),post))
    (sourceBound : LoopSteps.steps branchingLoopEntry {(concreteDeclLoopState arch source (twoPrograms name callee body)) with memory := memory} ≤ limit) :
    let crep := twoPrograms name callee body
    let loops := compileProgHOLExact arch crep
    let words := loopToWordCompileHOL loops
    let starter := {(phase3Starter arch source crep template heapLength 64 frame) with memory := memory}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2}
    let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL branchingLoopEntry .ln) (LoopToWord.toNumSetHOL []))) .ln
    let word := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
      (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
    compile wc ac words = compileWith Flapjack.RegAlloc.regAllocExecutable wc ac
      (loopToWordCompileHOL (twoLoopPrograms arch name callee body)) ∧
    ∃ wordPost wordResult,
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word (some (.result values)) post wordResult wordPost ∧
      target.1 = wordResult ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*limit+1, code := sptFromAList (compile wc ac words).2} ≤
        twoProgramWordBound arch name callee body limit wc ac := by
  let crep := twoPrograms name callee body
  let loops := compileProgHOLExact arch crep
  let words := loopToWordCompileHOL loops
  let starter := {(phase3Starter arch source crep template heapLength 64 frame) with memory := memory}
  let loop := {(concreteDeclLoopState arch source crep) with memory := memory}
  let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
    (sptDifference (accVarsHOL branchingLoopEntry .ln) (LoopToWord.toNumSetHOL []))) .ln
  let word := WordSemStateFiniteExact.callEnv [(.loc 1 0 : WordLocW 64)]
    (sptLookup 64 starter.stackSize) (WordSemStateFiniteExact.decClock starter)
  have loopEq : loops = twoLoopPrograms arch name callee body := by
    exact (twoLoopPrograms_eq arch name callee body shape).symm
  have facts := twoWordTables_facts arch name callee body fresh shape
  have starterFacts := phase3Starter_relations arch source crep template heapLength 64 frame memory heap
  have localFacts := phase3Starter_locals arch source crep template heapLength 64 frame branchingLoopEntry memory
  have codeEq : starter.code = sptFromAList words := rfl
  have entryMember : (64,1,(LoopToWord.compHOL ctxt branchingLoopEntry (64,2)).1) ∈ words := by
    change (64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry) ∈ words
    simpa [words,loopEq] using facts.1
  have calleeMember : (65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)) ∈ words := by
    simpa [words,loopEq] using facts.2.1
  have nodup : (words.map Prod.fst).Nodup := by simpa [words,loopEq] using facts.2.2.1
  have shapes : TailProgramShapes words := by simpa [words,loopEq] using facts.2.2.2.1
  have lookup : sptLookup 65 loop.code = some ([],twoCallee arch name callee body) := by
    change sptLookup 65 (sptFromAList loops) = _
    rw [loopEq]
    exact facts.2.2.2.2.2.2
  have calleeShape := twoCallee_shape arch name callee body shape
  have premises : evaluate branchingLoopEntry loop = (some (.result values),post) ∧
      some (LoopResultExact.result values) ≠ some LoopResultExact.error ∧ loopToWordStateRelHOLExact loop word ∧
      LoopToWord.localsRelHOL ctxt loop.locals word.locals ∧ sptLookup 0 word.locals = some (.loc 1 0) ∧
      goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL branchingLoopEntry .ln) → sptMem k ctxt) := by
    refine ⟨run,by simp,starterFacts.1,localFacts.1,localFacts.2.1,?_,by decide,localFacts.2.2⟩
    exact Or.inr rfl
  have span := singleTail_wholeWord_span entryShape calleeShape loop post (some (.result values))
    64 starter ctxt (64,2) limit words wc ac entryMember calleeMember nodup shapes codeEq
    starterFacts.2.1 starterFacts.2.2.1 starterFacts.2.2.2 lookup premises (.return values) sourceBound
  refine ⟨twoProgram_optimized_executable arch name callee body shape wc ac, ?_⟩
  rw [twoProgramWordBound_eq arch name callee body shape limit wc ac]
  simpa [twoProgramWordBoundSpec,crep,loops,words,starter,loop,ctxt,word,loopToWordCompFuncHOL] using span
end SteppedFlapjack.Concrete
