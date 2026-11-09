import SteppedFlapjack.WordAllocSteps.WholeProgram
import SteppedFlapjack.WordSimpSteps.TailCallBound
import Flapjack.Compiler.Backend.WordToWord.Proofs.NoInstallCompileSingle

/-! Code-table facts for whole programs with loop callees and tail-call entries. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps
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

/-- Every function is a supported call-free loop body or a direct tail entry. -/
def TailProgramShapes (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ name arity body, (name,arity,body) ∈ programs →
    LoopSequence body ∨ LoopLiveSteps.WordTailEntryShape body

/-- The actual compiler's output has the code relation and equal domain needed
for the tail-entry simulation; neither property is an extra hypothesis. -/
theorem wholeCompile_tail_codeRelations (wc : Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (shapes : TailProgramShapes programs) :
    WordProps.noInstallCode (sptFromAList programs) ∧
    WordProps.noMtCode (sptFromAList programs) ∧
    codeRel (sptFromAList programs) (sptFromAList (compile wc ac programs).2) ∧
    sptDomain (sptFromAList programs) = sptDomain (sptFromAList (compile wc ac programs).2) ∧
    WordProps.noInstallCode (sptFromAList (compile wc ac programs).2) := by
  have source : WordProps.noInstallCode (sptFromAList programs) ∧ WordProps.noMtCode (sptFromAList programs) := by
    constructor <;> intro name arity body lookup
    all_goals
      rw [sptLookup_sptFromAList] at lookup
      have member := sptAListLookup_mem name programs (arity,body) lookup
      rcases shapes name arity body member with h | h
      all_goals first | exact loopSequence_noInstall h | exact WordSimpSteps.tailEntry_noInstall h | exact loopSequence_noMt h | exact tailEntry_noMt h
  have rel : codeRel (sptFromAList programs) (sptFromAList (compile wc ac programs).2) :=
    no_mt_code_rel_ext _ _ ⟨source.2,code_rel_ext_word_to_word ac programs wc _ _ Prod.mk.eta.symm⟩
  have domain : sptDomain (sptFromAList programs) = sptDomain (sptFromAList (compile wc ac programs).2) := by
    rw [sptDomainFromAList,sptDomainFromAList,wholeCompile_names]
  exact ⟨source.1,source.2,rel,domain,noInstallCode_of_codeRel _ _ rel domain source.1⟩


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
