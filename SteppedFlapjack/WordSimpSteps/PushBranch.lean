import SteppedFlapjack.WordSimpSteps.ConstBranch

/-! The conditional push-out pass preserves loop-free branches. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack SteppedFlapjack.WordSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordSimp
variable {width : Nat} [NeZero width] {C F : Type}

/-- Push-out preserves branch shape whether or not an early exit is found. -/
theorem pushOutIfAux_branch {p : WordLangProgHOL (BitVec width)} (hp : Branch p) :
    Branch (pushOutIfAux p).1 := by
  induction hp with
  | assign dst e => exact .assign dst e
  | inst i => exact .inst i
  | move pri ms => exact .move pri ms
  | get dst n => exact .get dst n
  | set n e => exact .set n e
  | store e src => exact .store e src
  | skip => exact .skip
  | tick => exact .tick
  | ret r vs => exact .ret r vs
  | «break» n => exact .break n
  | «continue» n => exact .continue n
  | seq ha hb iha ihb =>
    simp only [pushOutIfAux]
    rcases h : pushOutIfAux _ with ⟨a, ba⟩
    simp only [h] at iha
    cases ba with
    | true => exact .seq iha hb
    | false =>
      rcases k : pushOutIfAux _ with ⟨b, bb⟩
      simp only [k] at ihb
      exact .seq iha ihb
  | ite cmp r ri ha hb iha ihb =>
    simp only [pushOutIfAux]
    rcases h : pushOutIfAux _ with ⟨a, ba⟩
    rcases k : pushOutIfAux _ with ⟨b, bb⟩
    simp only [h] at iha
    simp only [k] at ihb
    cases ba <;> cases bb <;> simp only
    · exact .ite cmp r ri iha ihb
    · exact .seq (.ite cmp r ri .skip ihb) iha
    · exact .seq (.ite cmp r ri iha .skip) ihb
    · exact .ite cmp r ri iha ihb

/-- Push-out produces at most its output syntax size times the original number
of Word visits on a loop-free branch. -/
theorem pushOutIf_branch_steps {p : WordLangProgHOL (BitVec width)} (hp : Branch p)
    (s : WordSemStateFiniteExact width C F) :
    steps (pushOutIf p) s ≤ sizeOf (pushOutIf p) * steps p s := by
  have shape : Branch (pushOutIf p) := pushOutIfAux_branch hp
  have h := branch_static shape s
  have positive := steps_pos p s
  nlinarith

end SteppedFlapjack.WordSimpSteps
