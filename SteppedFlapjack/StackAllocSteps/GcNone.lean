import SteppedFlapjack.StackSteps.Defs
import Flapjack.Compiler.Backend.StackAlloc.GcCode

/-! Bottom-up step bounds for stack allocation garbage-collector code. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemControl Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Bound a sequence using bounds valid for either intermediate state. -/
theorem stepsSeqLe (a b : HolProg width) (A B : Nat)
    (ha : ∀ s : StackSemStateFiniteExact width C F, steps (a,s) ≤ A)
    (hb : ∀ s : StackSemStateFiniteExact width C F, steps (b,s) ≤ B)
    (s : StackSemStateFiniteExact width C F) : steps (.seq a b,s) ≤ 1 + A + B := by
  rw [steps_seq]
  have h := ha s
  cases hx : fixClock s (evaluate (a,s)) with
  | mk r t =>
    cases r with
    | none => simp only; have ht := hb t; omega
    | some x => simp only; omega

/-- Bound either branch without assuming which comparison succeeds. -/
theorem stepsIteLe (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width) (A B : Nat)
    (ha : ∀ s : StackSemStateFiniteExact width C F, steps (a,s) ≤ A)
    (hb : ∀ s : StackSemStateFiniteExact width C F, steps (b,s) ≤ B)
    (s : StackSemStateFiniteExact width C F) : steps (.ite cmp r ri a b,s) ≤ 1 + A + B := by
  rw [steps_ite]
  have h1 := ha s
  have h2 := hb s
  split <;> try omega
  split <;> try omega

/-- The no-collector allocation code takes at most 15 StackSem steps. -/
theorem noneGcSteps (conf : Config) (hk : conf.gcKind = .none)
    (s : StackSemStateFiniteExact width C F) : steps (wordGcCode conf, s) ≤ 15 := by
  simp only [wordGcCode, hk, listSeqHOL, constInst]
  refine stepsSeqLe _ _ 1 13 ?_ ?_ s
  · intro t; exact Nat.le_of_eq (steps_leaf _ t rfl)
  · intro t; refine stepsSeqLe _ _ 1 11 ?_ ?_ t
    · intro t; exact Nat.le_of_eq (steps_leaf _ t rfl)
    · intro t; refine stepsSeqLe _ _ 1 9 ?_ ?_ t
      · intro t; exact Nat.le_of_eq (steps_leaf _ t rfl)
      · intro t; refine stepsSeqLe _ _ 1 7 ?_ ?_ t
        · intro t; exact Nat.le_of_eq (steps_leaf _ t rfl)
        · intro t; refine stepsSeqLe _ _ 1 5 ?_ ?_ t
          · intro t; exact Nat.le_of_eq (steps_leaf _ t rfl)
          · intro t; refine stepsIteLe _ _ _ _ _ 1 3 ?_ ?_ t
            · intro u; exact Nat.le_of_eq (steps_leaf _ u rfl)
            · intro u; refine stepsSeqLe _ _ 1 1 ?_ ?_ u
              · intro v; exact Nat.le_of_eq (steps_leaf _ v rfl)
              · intro v; exact Nat.le_of_eq (steps_leaf _ v rfl)

end SteppedFlapjack.StackAllocSteps
