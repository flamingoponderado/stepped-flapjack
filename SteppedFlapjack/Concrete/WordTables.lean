import SteppedFlapjack.Concrete.BranchEntryLoop
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape
import SteppedFlapjack.CrepToLoopSteps.ScalarExecutable
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

/-- The optimized Loop callee generated for a two-function scalar program. -/
def twoCallee (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64) : HolLoopProg 64 :=
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (twoPrograms name callee body)) 0
  optimiseScalar (compileHOLExact ctxt .ln body)

/-- The actual optimized table equals an executable calculation for every scalar
program, including every value of a countdown literal. -/
theorem twoProgram_optimized_executable (arch : AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (shape : ScalarProgram body) (wc : Config) (ac : AsmConfigExact 64) :
    compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))) =
      compileWith Flapjack.RegAlloc.regAllocExecutable wc ac (loopToWordCompileHOL (twoLoopPrograms arch name callee body)) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  rw [compileWith_eq_compile _ allocator, twoLoopPrograms_eq arch name callee body shape]

/-- The generated entry has one direct tail destination. -/
theorem entryShape : SingleTailEntryShape 65 branchingLoopEntry := by
  exact .mark (.seq (.branch (.mark .skip)) (.mark (.seq (.mark .call) (.branch (.mark .skip)))))

/-- The generated Loop table contains the fixed entry and optimized callee. -/
theorem twoLoops_exact (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64)
    (fresh : name ≠ callee) :
    twoLoopPrograms arch name callee body = [(64,[],branchingLoopEntry),(65,[],twoCallee arch name callee body)] := by
  have h := twoLoopPrograms_entry_code arch name callee body fresh
  simp only [twoLoopPrograms, firstLoopName, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h
  · have eq := h.2.2
    simp only [twoLoopPrograms,firstLoopName,twoCallee,eq]
  · omega

/-- Every generated scalar callee belongs to the recursive span fragment. -/
theorem twoCallee_shape (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64)
    (shape : ScalarProgram body) : LoopSequenceSource (twoCallee arch name callee body) := by
  unfold twoCallee
  let ctxt := mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (twoPrograms name callee body)) 0
  have raw := compile_scalar_program shape ctxt .ln
  rw [optimiseScalar_eq raw]
  exact compile_scalar_optimized_wordShape shape ctxt .ln

/-- The actual generated Word table discharges the span’s code and shape facts. -/
theorem twoWordTables_facts (arch : AsmArchitecture) (name callee : MlString) (body : CrepProgHOL 64)
    (fresh : name ≠ callee) (shape : ScalarProgram body) :
    let loops := twoLoopPrograms arch name callee body
    let calleeLoop := twoCallee arch name callee body
    let words := loopToWordCompileHOL loops
    let entryWord := loopToWordCompFuncHOL 64 [] branchingLoopEntry
    let calleeWord := loopToWordCompFuncHOL 65 [] calleeLoop
    (64,1,entryWord) ∈ words ∧ (65,1,calleeWord) ∈ words ∧
    (words.map Prod.fst).Nodup ∧ TailProgramShapes words ∧
    AllowedTailEntry (fun n => n = 65) entryWord ∧ LoopSequence calleeWord ∧
    sptLookup 65 (sptFromAList loops) = some ([],calleeLoop) := by
  have loopEq := twoLoops_exact arch name callee body fresh
  have calleeShape := twoCallee_shape arch name callee body shape
  have wordEq : loopToWordCompileHOL (twoLoopPrograms arch name callee body) =
      [(64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),
       (65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body))] := by
    rw [loopEq]
    rfl
  have allowed : AllowedTailEntry (fun n => n = 65) (loopToWordCompFuncHOL 64 [] branchingLoopEntry) := by
    unfold loopToWordCompFuncHOL
    exact singleTail_word_allowed entryShape _ _
  have wordShape : LoopSequence (loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)) := by
    unfold loopToWordCompFuncHOL
    exact loopSequenceSource_word calleeShape _ _
  have entryWordShape : WordTailEntryShape (loopToWordCompFuncHOL 64 [] branchingLoopEntry) := by
    unfold loopToWordCompFuncHOL
    exact tailEntry_word (singleTail_to_tail entryShape) _ _
  have allShapes : TailProgramShapes (loopToWordCompileHOL (twoLoopPrograms arch name callee body)) := by
    rw [wordEq]
    intro n arity p member
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · exact Or.inr entryWordShape
    · exact Or.inl wordShape
  dsimp only
  refine ⟨?_,?_,?_,allShapes,allowed,wordShape,?_⟩
  · rw [wordEq]; simp
  · rw [wordEq]; simp
  · rw [wordEq]; simp
  · rw [loopEq]; simp [sptLookup_sptFromAList,sptAListLookup]

end SteppedFlapjack.Concrete
