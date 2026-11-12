import SteppedFlapjack.WordAllocSteps.WholeProgram
import SteppedFlapjack.WordAllocSteps.TailShape
import SteppedFlapjack.WordSimpSteps.TailCallBound
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode
import Flapjack.Pancake.Proofs.PanToTarget.WordToWordNoInstall

/-! Code-table facts for whole programs with loop callees and tail-call entries. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSteps
open Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
variable {width : Nat} [NeZero width]

private theorem branch_noMt {p : WordLangProgHOL (BitVec width)} (h : Branch p) :
    noMtSubprogsHOL p = true := by
  induction h <;> simp_all [noMtSubprogsHOL,notCreatedSubprogsWithMemOp]

private theorem loopSequence_noMt {p : WordLangProgHOL (BitVec width)} (h : LoopSequence p) :
    noMtSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noMt h
  | loop names exits h => simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using branch_noMt h
  | seq _ _ a b =>
    simp only [noMtSubprogsHOL] at a b ⊢
    simp only [notCreatedSubprogsWithMemOp,a,b,Bool.and_self]
  | nestedLoop names exits h ih => simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using ih
  | conditional cmp r ri ha hb iha ihb =>
    simp only [noMtSubprogsHOL] at iha ihb ⊢
    simp only [notCreatedSubprogsWithMemOp,iha,ihb,Bool.and_self]

private theorem tailEntry_noMt {p : WordLangProgHOL (BitVec width)}
    (h : LoopLiveSteps.WordTailEntryShape p) : noMtSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noMt h
  | call loc => rfl
  | seq _ _ a b =>
    simp only [noMtSubprogsHOL] at a b ⊢
    simp only [notCreatedSubprogsWithMemOp,a,b,Bool.and_self]

private theorem branch_noAlloc {p : WordLangProgHOL (BitVec width)} (h : Branch p) :
    noAllocSubprogsHOL p = true := by
  induction h <;> simp_all [noAllocSubprogsHOL,notCreatedSubprogsWithMemOp]

private theorem loopSequence_noAlloc {p : WordLangProgHOL (BitVec width)} (h : LoopSequence p) :
    noAllocSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noAlloc h
  | loop names exits h => simpa [noAllocSubprogsHOL,notCreatedSubprogsWithMemOp] using branch_noAlloc h
  | nestedLoop names exits h ih => simpa [noAllocSubprogsHOL,notCreatedSubprogsWithMemOp] using ih
  | seq _ _ a b | conditional _ _ _ _ _ a b =>
    simp only [noAllocSubprogsHOL] at a b ⊢
    simp only [notCreatedSubprogsWithMemOp,a,b,Bool.and_self]

private theorem tailEntry_noAlloc {p : WordLangProgHOL (BitVec width)}
    (h : LoopLiveSteps.WordTailEntryShape p) : noAllocSubprogsHOL p = true := by
  induction h with
  | branch h => exact branch_noAlloc h
  | call loc => rfl
  | seq _ _ a b =>
    simp only [noAllocSubprogsHOL] at a b ⊢
    simp only [notCreatedSubprogsWithMemOp,a,b,Bool.and_self]

/-- Every function is a supported call-free loop body or a direct tail entry. -/
def TailProgramShapes (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ name arity body, (name,arity,body) ∈ programs →
    LoopSequence body ∨ LoopLiveSteps.WordTailEntryShape body

/-- Safety properties required by the whole-program Word optimizer. -/
def WordProgramSafety (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) : Prop :=
  WordProps.noInstallCode (sptFromAList programs) ∧ WordProps.noMtCode (sptFromAList programs) ∧
    WordProps.noAllocCode (sptFromAList programs)

/-- Existing tail-entry programs satisfy the whole-program safety properties. -/
theorem tailProgram_safety (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (shapes : TailProgramShapes programs) : WordProgramSafety programs := by
  refine ⟨?_,?_,?_⟩ <;> intro name arity body lookup
  all_goals
    rw [sptLookup_sptFromAList] at lookup
    have member := sptAListLookup_mem name programs (arity,body) lookup
    rcases shapes name arity body member with h | h
    all_goals first | exact loopSequence_noInstall h | exact WordSimpSteps.tailEntry_noInstall h |
      exact loopSequence_noMt h | exact tailEntry_noMt h | exact loopSequence_noAlloc h | exact tailEntry_noAlloc h

/-- Every actual Loop-to-Word function table satisfies these safety properties,
including functions with ordinary and tail calls. -/
theorem loopToWord_programSafety (programs : List (Nat × List Nat × HolLoopProg width)) :
    WordProgramSafety (loopToWordCompileHOL programs) := by
  exact ⟨LoopToWord.loop_compile_no_install_code programs, LoopToWord.loop_compile_no_mt_code programs,
    LoopToWord.loop_compile_no_alloc_code programs⟩

/-- The actual whole-program Word compiler preserves the code domain and
provides the semantic code relation for every safe input table. -/
theorem wholeCompile_codeRelations (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (safety : WordProgramSafety programs) :
    WordProps.noInstallCode (sptFromAList programs) ∧
    WordProps.noMtCode (sptFromAList programs) ∧
    codeRel (sptFromAList programs) (sptFromAList (compile wc ac programs).2) ∧
    sptDomain (sptFromAList programs) = sptDomain (sptFromAList (compile wc ac programs).2) ∧
    WordProps.noInstallCode (sptFromAList (compile wc ac programs).2) ∧
    WordProps.noAllocCode (sptFromAList programs) := by
  obtain ⟨noInstall,noMt,noAlloc⟩ := safety
  have rel : codeRel (sptFromAList programs) (sptFromAList (compile wc ac programs).2) :=
    no_mt_code_rel_ext _ _ ⟨noMt,code_rel_ext_word_to_word ac programs wc _ _ Prod.mk.eta.symm⟩
  have domain : sptDomain (sptFromAList programs) = sptDomain (sptFromAList (compile wc ac programs).2) := by
    rw [sptDomainFromAList,sptDomainFromAList,wholeCompile_names]
  exact ⟨noInstall,noMt,rel,domain,noInstallCode_of_codeRel _ _ rel domain noInstall,noAlloc⟩


private theorem noMtCode_of_codeRel
    (code target : Spt (Nat × WordLangProgHOL (BitVec width)))
    (rel : codeRel code target) (dom : sptDomain code = sptDomain target)
    (safe : WordProps.noMtCode code) : WordProps.noMtCode target := by
  intro k n p hk
  have hm : (sptLookup k code).isSome = true := by
    have h := congrFun dom k
    simp only [sptDomain] at h
    rw [h, hk]
    rfl
  rcases hv : sptLookup k code with _ | ⟨ar,e⟩
  · rw [hv] at hm; cases hm
  obtain ⟨col,t,kk,a,c,h⟩ := rel k _ hv
  rw [hk] at h
  have hp : p = (compileSingle t kk a c ((k,ar,e),col)).2.2 :=
    congrArg (·.2) (Option.some.inj h)
  have he := safe k ar e hv
  rw [hp, noMtSubprogsHOL_eq_notCreated] at *
  exact WordConvs.compile_single_not_created_subprogs _ t kk a c ((k,ar,e),col) he

/-- Whole-program Word optimization preserves the table safety properties,
including for tables containing ordinary and tail calls. -/
theorem wholeCompile_targetSafety (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (safety : WordProgramSafety programs) :
    WordProgramSafety (compile wc ac programs).2 := by
  obtain ⟨_,noMt,rel,dom,noInstall,noAlloc⟩ := wholeCompile_codeRelations wc ac programs safety
  exact ⟨noInstall, noMtCode_of_codeRel _ _ rel dom noMt,
    PanToTarget.noAllocCode_of_codeRel _ _ rel dom noAlloc⟩


/-- Starting from the same explicit clock, whole-program Word optimization
preserves the start-call result and events for a supported code table and
bounds the optimized run using the concrete output table. -/
theorem wholeCompile_start_agrees {C F : Type} (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (safety : WordProgramSafety programs) (s : WordSemStateFiniteExact width C F)
    (start clock : Nat) (code : s.code = sptFromAList programs)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (stack : s.stack = [])
    (nonerror : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {s with clock := clock}).1 ≠ some .error) :
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        {s with clock := clock, code := sptFromAList (compile wc ac programs).2}).1 =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {s with clock := clock}).1 ∧
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        {s with clock := clock, code := sptFromAList (compile wc ac programs).2}).2.ffi =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) {s with clock := clock}).2.ffi ∧
    steps (.call none (some start) [0] none)
      {s with clock := clock, code := sptFromAList (compile wc ac programs).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compile wc ac programs).2)) * clock := by
  have safe := wholeCompile_targetSafety wc ac programs safety
  have bound := wordTable_clock_bound (.call none (some start) [0] none)
    {s with clock := clock,code := sptFromAList (compile wc ac programs).2} rfl rfl safe.2.1 safe.1
  obtain ⟨noInstall,noMt,relation,domain,_,noAlloc⟩ := wholeCompile_codeRelations wc ac programs safety
  rw [← code] at noInstall noMt relation domain noAlloc
  have agree := Flapjack.Compiler.Backend.WordToWord.compile_runs_agree s _ start clock relation
    noInstall noAlloc noMt domain gc stack nonerror
  exact ⟨agree.1,agree.2,by simpa [wordControlWeight] using bound⟩

/-- Actual Loop-to-Word function tables preserve start-call results and events through Word optimization. -/
theorem wholeCompile_loopToWord_start_agrees {width : Nat} [NeZero width] {C F : Type}
    (wc : Config) (ac : AsmConfigExact width) (programs : List (Nat × List Nat × HolLoopProg width))
    (s : WordSemStateFiniteExact width C F) (start clock : Nat)
    (code : s.code = sptFromAList (loopToWordCompileHOL programs))
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun) (stack : s.stack = [])
    (nonerror : (evaluate (.call none (some start) [0] none) {s with clock := clock}).1 ≠ some .error) :
    (evaluate (.call none (some start) [0] none)
      {s with clock := clock, code := sptFromAList (compile wc ac (loopToWordCompileHOL programs)).2}).1 =
      (evaluate (.call none (some start) [0] none) {s with clock := clock}).1 ∧
    (evaluate (.call none (some start) [0] none)
      {s with clock := clock, code := sptFromAList (compile wc ac (loopToWordCompileHOL programs)).2}).2.ffi =
      (evaluate (.call none (some start) [0] none) {s with clock := clock}).2.ffi ∧
    steps (.call none (some start) [0] none)
      {s with clock := clock, code := sptFromAList (compile wc ac (loopToWordCompileHOL programs)).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compile wc ac (loopToWordCompileHOL programs)).2)) * clock := by
  exact wholeCompile_start_agrees wc ac (loopToWordCompileHOL programs)
    (loopToWord_programSafety programs) s start clock code gc stack nonerror

/-- Distinct function names identify both the source body and the body produced
with the actual compiler-selected colour in the whole-program code tables. -/
theorem wholeCompile_entry_lookups (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name arity : Nat) (body : WordLangProgHOL (BitVec width))
    (member : (name,arity,body) ∈ programs) (nodup : (programs.map Prod.fst).Nodup) :
    sptLookup name (sptFromAList programs) = some (arity,body) ∧
    sptLookup name (sptFromAList (compile wc ac programs).2) =
      some (arity,(fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length))
        wc.regAlg ac ((name,arity,body),entryColour wc programs name)).2.2) := by
  have outputNodup : ((compile wc ac programs).2.map Prod.fst).Nodup := by
    rw [wholeCompile_names]
    exact nodup
  have outputMember := wholeCompile_contains_entryColour wc ac programs name arity body member nodup
  have outputEntry : (name,arity,(fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,arity,body),entryColour wc programs name)).2.2) ∈ (compile wc ac programs).2 := by
    simpa [fullCompileSingle,compileSingle] using outputMember
  constructor
  · rw [sptLookup_sptFromAList]
    exact sptAListLookup_of_mem_nodup programs name (arity,body) nodup member
  · rw [sptLookup_sptFromAList]
    exact sptAListLookup_of_mem_nodup _ name _ outputNodup outputEntry

end SteppedFlapjack.WordAllocSteps
