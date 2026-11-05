import SteppedFlapjack.StackRemoveSteps.OracleRunEvaluate
/-! Provenance of code through installation and sequential transitions. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSemEvaluate
variable {width : Nat} [NeZero width] {C F : Type}

/-- Every code entry in `t` originates in `s` or one of the first `used` oracle entries. -/
def codeOrigin (s t : StackSemStateFiniteExact width C F) (used : Nat) : Prop :=
  ∀ label program, sptLookup label t.code = some program →
    sptLookup label s.code = some program ∨
      ∃ index < used, ∃ name, (name, program) ∈ (s.compileOracle index).2.1

theorem codeOrigin_same (s t : StackSemStateFiniteExact width C F) (n : Nat)
    (hcode : t.code = s.code) : codeOrigin s t n := by
  intro label program h
  left
  simpa only [hcode] using h

theorem codeOrigin_trans (s middle post : StackSemStateFiniteExact width C F) (first second : Nat)
    (hfirst : codeOrigin s middle first) (hsecond : codeOrigin middle post second)
    (horacle : middle.compileOracle = holShiftSeq first s.compileOracle) :
    codeOrigin s post (first + second) := by
  intro label program h
  rcases hsecond label program h with hm | ⟨index, hi, name, hmem⟩
  · rcases hfirst label program hm with hs | ⟨index, hi, name, hmem⟩
    · exact Or.inl hs
    · exact Or.inr ⟨index, by omega, name, hmem⟩
  · right
    refine ⟨index + first, by omega, name, ?_⟩
    rw [horacle] at hmem
    exact hmem

theorem codeOrigin_install (ptr len dptr dlen ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.install ptr len dptr dlen ret : HolProg width), s) = (r, t)) :
    (t.compileOracle = s.compileOracle ∧ codeOrigin s t 0) ∨
    (t.compileOracle = holShiftSeq 1 s.compileOracle ∧ codeOrigin s t 1) := by
  rcases evaluate_install_effect ptr len dptr dlen ret s t r h with same | installed
  · exact Or.inl ⟨same.2.1, codeOrigin_same s t 0 same.1⟩
  · refine Or.inr ⟨installed.2.1, ?_⟩
    intro label program hlookup
    rw [installed.1, sptLookup_sptUnion] at hlookup
    cases hc : sptLookup label s.code with
    | some value =>
      simp only [hc, Option.some.injEq] at hlookup
      subst value
      exact Or.inl rfl
    | none =>
      simp only [hc] at hlookup
      rw [sptLookup_sptFromAList] at hlookup
      exact Or.inr ⟨0, by omega, label, sptAListLookup_mem label _ program hlookup⟩
/-- A finite initial code/oracle bound covers every code entry with a tracked origin. -/
theorem codeOrigin_bound {B K n used : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F) (origin : codeOrigin s t used)
    (hused : used ≤ n) (hcode : codeBound B bounds K s)
    (horacle : oraclePrefixBound B bounds K n s) : codeBound B bounds K t := by
  intro label program hlookup
  rcases origin label program hlookup with hc | ⟨index, hi, name, hm⟩
  · exact hcode label program hc
  · exact horacle index (by omega) name program hm

end SteppedFlapjack.StackRemoveSteps.CompCorrect
