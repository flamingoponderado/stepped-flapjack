import SteppedFlapjack.PanToCrepSteps.WhileSequence
import SteppedFlapjack.CrepToLoopSteps.BranchWhileRiscV

/-! Pancake initialization, loop and continuation through the frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- An initial source branch can be followed by the bounded loop/continuation;
early exits in the initialization are included. -/
theorem branchWhileBranch_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (condition : ExpHOL width) (body tail : ProgHOL width)
    (context : PanToCrepContextExact width) (initShape : BranchProgram context init)
    (conditionShape : ScalarExpression context condition) (bodyShape : BranchProgram context body)
    (tailShape : BranchProgram context tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.seq init (.seq (.while condition body) tail)) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.seq init (.seq (.while condition body) tail)) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.seq init (.seq (.while condition body) tail))) target ≤
      (3 + sizeOf (compileProgExactHOLW context init) + sizeOf (compileProgExactHOLW context body) +
        sizeOf (compileProgExactHOLW context tail)) *
        controlSteps (.seq init (.seq (.while condition body) tail)) source := by
  have locs : localisedProgHOL init = true ∧ localisedProgHOL (.seq (.while condition body) tail) = true := by
    simpa [localisedProgHOL] using localised
  have seqRun := run
  rw [evaluateHOLFiniteState_seq_line780] at seqRun
  rcases firstRun : source.evaluateHOLFiniteState init with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  dsimp only at seqRun
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    exact nonerror (Prod.mk.inj seqRun).1.symm
  have sourceCount := controlSteps_seq init (.seq (.while condition body) tail) source
  rw [firstRun] at sourceCount
  have correct : pcCompileCorrectAt init source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetPost,targetRun,postState,postCode,postExcp,resultRel⟩ :=
    correct firstResult middle target context firstRun firstNonerror stateRel codeRel excpRel localsRel locs.1
  rw [compileProgExactHOLW,CrepSteps.steps_seq,targetRun]
  have initBound := CrepSteps.branchProgram_static (branch_compile initShape) target
  cases firstResult with
  | none =>
    obtain ⟨rfl,postLocals⟩ := resultRel
    simp only
    have restBound := whileThenBranch_compiled_steps condition body tail context conditionShape bodyShape tailShape
      middle sourceFinal result targetPost seqRun nonerror postState postCode postExcp postLocals locs.2
    simp only at sourceCount
    nlinarith
  | some r =>
    have notNone : targetResult ≠ none := by
      intro bad
      subst targetResult
      cases r with
      | exception eid value =>
        simp only [pcCompileCorrectResultRel] at resultRel
        split at resultRel
        · exact resultRel.elim
        · exact absurd resultRel.1 (by simp)
      | _ => simp [pcCompileCorrectResultRel] at resultRel
    cases targetResult with
    | none => exact (notNone rfl).elim
    | some t =>
      simp only
      simp only at sourceCount
      have positive := controlSteps_pos (.seq init (.seq (.while condition body) tail)) source
      nlinarith

end SteppedFlapjack.PanToCrepSteps
