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
/-- A uniform bound for all looked-up functions bounds the table maximum. -/
private theorem wordCodeWeight_le (code : Spt (Nat × WordLangProgHOL (BitVec 64))) (limit : Nat)
    (positive : 1 ≤ limit)
    (entries : ∀ loc arity body, sptLookup loc code = some (arity,body) → wordControlWeight body ≤ limit) :
    wordCodeWeight code ≤ limit := by
  unfold wordCodeWeight
  have aux : ∀ rows : List (Nat × (Nat × WordLangProgHOL (BitVec 64))),
      (∀ row ∈ rows, wordControlWeight row.2.2 ≤ limit) →
      rows.foldr (fun row weight => max (wordControlWeight row.2.2) weight) 1 ≤ limit := by
    intro rows bound
    induction rows with
    | nil => exact positive
    | cons row rest ih =>
      simp only [List.foldr_cons,Nat.max_le]
      exact ⟨bound row (by simp),ih (fun r hr => bound r (by simp [hr]))⟩
  apply aux
  intro row member
  exact entries row.1 row.2.1 row.2.2 ((sptToAList_mem_iff_lookup code row.1 row.2).mp member)

private theorem wordWeight_positive (p : WordLangProgHOL (BitVec 64)) : 1 ≤ wordControlWeight p := by
  cases p <;> (try simp only [wordControlWeight]) <;> try omega
  case call ret dest args handler =>
    cases ret <;> cases handler <;> simp [wordControlWeight]
    all_goals omega

private theorem sequence_to_simple {p : HolLoopProg 64} (shape : LoopSequenceSource p) :
    SimpleLoopSequenceSource p := by
  induction shape with
  | branch h => exact .branch h
  | loop live exits h => exact .loop live exits (.branch h)
  | seq _ _ a b => exact .seq a b
  | nestedLoop live exits _ ih => exact .loop live exits ih
  | conditional cmp r ri live _ _ a b => exact .conditional cmp r ri live a b

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
  have loopTable : LoopTableSupported loop.code := by
    change LoopTableSupported (sptFromAList loops)
    rw [loopEq,twoLoops_exact arch name callee body fresh]
    intro loc params prog found
    rw [sptLookup_sptFromAList] at found
    have member := sptAListLookup_mem loc
      [(64,[],branchingLoopEntry),(65,[],twoCallee arch name callee body)] (params,prog) found
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · exact tailEntry_to_simple (singleTail_to_tail entryShape)
    · exact sequence_to_simple calleeShape
  have span := loopTable_wholeWord_span (tailEntry_to_simple (singleTail_to_tail entryShape))
    loop post (some (.result values)) loopTable 64 starter ctxt (64,2) limit words wc ac entryMember nodup
    (tailProgram_safety words shapes) codeEq starterFacts.2.1 starterFacts.2.2.1 starterFacts.2.2.2
    premises (.return values) sourceBound
  let entryOut := (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
    ((64,1,(LoopToWord.compHOL ctxt branchingLoopEntry (64,2)).1),entryColour wc words 64)).2.2
  let calleeOut := (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
    ((65,1,loopToWordCompFuncHOL 65 [] (twoCallee arch name callee body)),entryColour wc words 65)).2.2
  have entryLookup := (wholeCompile_entry_lookups wc ac words 64 1 _ entryMember nodup).2
  have calleeLookup := (wholeCompile_entry_lookups wc ac words 65 1 _ calleeMember nodup).2
  have names : ((compile wc ac words).2.map Prod.fst) = [64,65] := by
    rw [wholeCompile_names]
    simp [words,loopEq,twoLoops_exact arch name callee body fresh,loopToWordCompileHOL,loopToWordCompileProgHOL]
  have entryPositive : 1 ≤ wordControlWeight entryOut := wordWeight_positive entryOut
  have calleePositive : 1 ≤ wordControlWeight calleeOut := wordWeight_positive calleeOut
  have entryLe : wordControlWeight entryOut ≤ wordControlWeight entryOut * (wordControlWeight calleeOut + 1) := by nlinarith
  have calleeLe : wordControlWeight calleeOut ≤ wordControlWeight entryOut * (wordControlWeight calleeOut + 1) := by nlinarith
  have tableBound : wordCodeWeight (sptFromAList (compile wc ac words).2) ≤
      wordControlWeight entryOut * (wordControlWeight calleeOut+1) := by
    apply wordCodeWeight_le _ _ (by nlinarith)
    intro loc arity prog found
    have member := sptAListLookup_mem loc (compile wc ac words).2 (arity,prog)
      (by simpa [sptLookup_sptFromAList] using found)
    have locMember : loc ∈ [64,65] := by
      rw [← names]
      exact List.mem_map.mpr ⟨_,member,rfl⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at locMember
    rcases locMember with rfl | rfl
    · rw [found] at entryLookup
      have equal := Option.some.inj entryLookup
      have : prog = entryOut := by simpa [entryOut] using congrArg Prod.snd equal
      simpa [this] using entryLe
    · rw [found] at calleeLookup
      have equal := Option.some.inj calleeLookup
      have : prog = calleeOut := by simpa [calleeOut] using congrArg Prod.snd equal
      simpa [this] using calleeLe
  have total : max 1 (wordCodeWeight (sptFromAList (compile wc ac words).2)) ≤
      wordControlWeight entryOut * (wordControlWeight calleeOut+1) := by
    exact Nat.max_le.mpr ⟨by nlinarith,tableBound⟩
  obtain ⟨wordPost,wordResult,relation,result,ffi,bound⟩ := span
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  rw [compileWith_eq_compile _ allocator] at bound
  refine ⟨twoProgram_optimized_executable arch name callee body shape wc ac,wordPost,wordResult,relation,result,ffi,?_⟩
  rw [twoProgramWordBound_eq arch name callee body shape limit wc ac]
  change _ ≤ 1 + wordControlWeight entryOut * (wordControlWeight calleeOut+1) * (6*limit+2)
  calc
    _ ≤ 1 + max 1 (wordCodeWeight (sptFromAList (compile wc ac words).2)) * (6*limit+1) := bound
    _ ≤ 1 + (wordControlWeight entryOut * (wordControlWeight calleeOut+1)) * (6*limit+1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ total) _
    _ ≤ 1 + (wordControlWeight entryOut * (wordControlWeight calleeOut+1)) * (6*limit+2) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
end SteppedFlapjack.Concrete
