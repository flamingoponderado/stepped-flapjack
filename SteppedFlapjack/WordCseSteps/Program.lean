import SteppedFlapjack.WordCseSteps.Leaves

/-! CSE output shape and visit bounds for branch-bodied loop sequences. -/
namespace SteppedFlapjack.WordCseSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordCse SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- CSE turns a supported branch into another supported branch for every
input knowledge state. -/
theorem wordCse_branch {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    ∀ data, Branch (wordCse data p).2 := by
  induction shape with
  | assign dst e => intro data; exact .assign _ _
  | store e src => intro data; exact .store _ _
  | skip => intro data; exact .skip
  | tick => intro data; exact .tick
  | ret r vs => intro data; exact .ret _ _
  | «break» n => intro data; exact .break _
  | «continue» n => intro data; exact .continue _
  | move pri ms => intro data; exact .move _ _
  | get dst n => intro data; exact getClause_branch data dst n
  | set n e => intro data; exact setClause_branch data n e
  | inst i =>
    intro data
    simp only [wordCse]
    rcases h : wordCseInst data (Flapjack.Compiler.Encoders.Asm.HolInst.ofWordLangInst i) with ⟨d,q⟩
    have hq := wordCseInst_branch data (Flapjack.Compiler.Encoders.Asm.HolInst.ofWordLangInst i)
    simpa only [h] using hq
  | opCurrHeap op dst src =>
    intro data
    simp only [wordCse]
    split
    · exact .opCurrHeap _ _ _
    · exact addToDataAux_branch _ _ _ (.opCurrHeap _ _ _)
  | @seq a b ha hb iha ihb =>
    intro data
    simp only [wordCse]
    rcases h : wordCse data a with ⟨da,a'⟩
    rcases k : wordCse da b with ⟨db,b'⟩
    have aa := iha data
    have bb := ihb da
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb
  | @ite cmp r ri a b ha hb iha ihb =>
    intro data
    simp only [wordCse]
    rcases h : wordCse data a with ⟨da,a'⟩
    rcases k : wordCse data b with ⟨db,b'⟩
    have aa := iha data
    have bb := ihb data
    simp only [h] at aa
    simp only [k] at bb
    exact .ite cmp r ri aa bb

/-- CSE preserves sequences of branches and branch-bodied loops. -/
theorem wordCse_loopSequence {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ data, LoopSequence (wordCse data p).2 := by
  induction shape with
  | branch hp => intro data; exact .branch (wordCse_branch hp data)
  | loop names exits hb =>
    intro data
    simp only [wordCse]
    rcases h : wordCse emptyData _ with ⟨d,q⟩
    have hb' := wordCse_branch hb emptyData
    simp only [h] at hb'
    exact .loop names exits hb'
  | @seq a b ha hb iha ihb =>
    intro data
    simp only [wordCse]
    rcases h : wordCse data a with ⟨da,a'⟩
    rcases k : wordCse da b with ⟨db,b'⟩
    have aa := iha data
    have bb := ihb da
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb

/-- Actual CSE output visits are bounded by its syntax size and source clock. -/
theorem wordCse_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) :
    steps (wordCommonSubexpElim p) s ≤ sizeOf (wordCommonSubexpElim p) * (s.clock+1) :=
  loopSequence_clock_bound (wordCse_loopSequence shape emptyData) s

end SteppedFlapjack.WordCseSteps
