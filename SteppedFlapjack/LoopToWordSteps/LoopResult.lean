import SteppedFlapjack.LoopToWordSteps.SixBound

/-! Result classification for the Loop-to-Word loop induction. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord.CompileCorrect

/-- A non-continuing, non-error Loop body cannot compile to a continuing
Word loop-body result. -/
theorem resultCase_noncontinuing {width : Nat} [NeZero width] {C F : Type}
    (ctxt : Spt Nat) (retv : WordLocW width) (word wordPost : WordSemStateFiniteExact width C F)
    (loopPost : LoopSemStateFiniteExact width F) (loopResult : Option (LoopResultExact width))
    (wordResult : Option (WordSemResult width))
    (relation : resultCase ctxt retv word loopResult loopPost wordResult wordPost)
    (notError : loopResult ≠ some .error)
    (stops : loopResult ≠ none ∧ loopResult ≠ some (.continue 0)) :
    wordSemContLoop wordResult = false := by
  cases loopResult with
  | none => exact False.elim (stops.1 rfl)
  | some r =>
    cases r with
    | «continue» n =>
      have nz : n ≠ 0 := by intro h; subst n; exact stops.2 rfl
      simp only [resultCase] at relation
      rw [relation.2.1]
      simp [wordSemContLoop,nz]
    | «break» n =>
      simp only [resultCase] at relation
      rw [relation.2.1]
      simp [wordSemContLoop]
    | result values =>
      simp only [resultCase] at relation
      rw [relation.2.1]
      rfl
    | exception value =>
      simp only [resultCase] at relation
      by_cases err : wordResult = some .error
      · rw [err]; rfl
      · obtain ⟨l,v,eq⟩ := relation.2.1 err
        rw [eq]
        rfl
    | timeOut =>
      simp only [resultCase] at relation
      rw [relation]
      rfl
    | finalFfi event =>
      simp only [resultCase] at relation
      rw [relation]
      rfl
    | error => exact False.elim (notError rfl)

end SteppedFlapjack.LoopToWordSteps
