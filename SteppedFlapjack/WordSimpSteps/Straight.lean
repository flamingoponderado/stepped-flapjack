import SteppedFlapjack.WordSimpSteps.Sequence
import Flapjack.Compiler.Backend.WordSimp.Proofs.CompileExp

/-! The complete WordSimp pass on straight-line Word code. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Constant propagation leaves straight instructions unchanged, although it
updates its internal constant map. -/
theorem constFpLoop_straight {p : WordLangProgHOL (BitVec width)} (hp : Straight p) :
    ∀ cs, (constFpLoop p cs).1 = p := by
  induction hp with
  | seq ha hb iha ihb =>
    intro cs
    simp only [constFpLoop]
    rcases h : constFpLoop _ cs with ⟨a, cs'⟩
    rcases k : constFpLoop _ cs' with ⟨b, cs''⟩
    have aa := iha cs
    have bb := ihb cs'
    simp only [h] at aa
    simp only [k] at bb
    simp only
    rw [aa, bb]
  | inst i => intro cs; rfl
  | move priority moves => intro cs; rfl
  | get dst name => intro cs; rfl
  | setVar name src => intro cs; rfl
  | opCurrHeap op dst src => intro cs; rfl
  | skip => intro cs; rfl

/-- Straight code is never itself a conditional. -/
theorem destIf_straight {p : WordLangProgHOL (BitVec width)} (hp : Straight p) :
    destIf p = none := by
  cases hp <;> rfl

/-- Duplicate-conditional hoisting leaves straight code unchanged. -/
theorem simpDuplicateIf_straight {p : WordLangProgHOL (BitVec width)} (hp : Straight p) :
    simpDuplicateIf p = p := by
  induction hp with
  | seq ha hb iha ihb =>
    simp only [simpDuplicateIf, iha, ihb, tryIfHoist1, destIf_straight hb]
  | inst i => rfl
  | move priority moves => rfl
  | get dst name => rfl
  | setVar name src => rfl
  | opCurrHeap op dst src => rfl
  | skip => rfl

/-- Straight code cannot trigger an early-exit conditional push-out. -/
theorem pushOutIfAux_straight {p : WordLangProgHOL (BitVec width)} (hp : Straight p) :
    pushOutIfAux p = (p, false) := by
  induction hp with
  | seq ha hb iha ihb => simp only [pushOutIfAux, iha, ihb]
  | inst i => rfl
  | move priority moves => rfl
  | get dst name => rfl
  | setVar name src => rfl
  | opCurrHeap op dst src => rfl
  | skip => rfl

/-- On straight-line code, all of the actual WordSimp pass is just sequence
normalization. -/
theorem compileExp_straight {p : WordLangProgHOL (BitVec width)} (hp : Straight p) :
    compileExp p = seqAssoc .skip p := by
  have shape := seqAssoc_straight hp Straight.skip
  simp only [Compiler.Backend.WordSimp.compileExp, constFp, constFpLoop_straight shape,
    simpDuplicateIf_straight shape, pushOutIf, pushOutIfAux_straight shape]

/-- The complete WordSimp pass preserves execution and has a source-relative
visit bound for straight-line Word programs. -/
theorem compileExp_straight_correct {p : WordLangProgHOL (BitVec width)}
    (hp : Straight p) (s : WordSemStateFiniteExact width C F) :
    evaluate (compileExp p) s = evaluate p s ∧
    steps (compileExp p) s ≤ sizeOf (seqAssoc .skip p) * steps p s := by
  rw [compileExp_straight hp]
  exact ⟨evaluate_Seq_assoc p s, seqAssoc_straight_steps hp s⟩

end SteppedFlapjack.WordSimpSteps
