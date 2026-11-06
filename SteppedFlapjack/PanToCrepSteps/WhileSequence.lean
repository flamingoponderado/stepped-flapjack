import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.CrepToLoopSteps.WhileSequenceRiscV

/-! Pancake loop plus continuation through the frontend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- The compiler preserves a source-step bound for a while followed by a
loop-free branch, whether the loop exits normally or propagates a result. -/
theorem whileThenBranch_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body tail : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : ScalarExpression context condition) (bodyShape : BranchProgram context body)
    (tailShape : BranchProgram context tail)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.seq (.while condition body) tail) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.seq (.while condition body) tail) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.seq (.while condition body) tail)) target ≤
      (2 + sizeOf (compileProgExactHOLW context body) + sizeOf (compileProgExactHOLW context tail)) *
        controlSteps (.seq (.while condition body) tail) source := by
  have locs : localisedProgHOL (.while condition body) = true ∧ localisedProgHOL tail = true := by
    simpa [localisedProgHOL] using localised
  have seqRun := run
  rw [evaluateHOLFiniteState_seq_line780] at seqRun
  rcases firstRun : source.evaluateHOLFiniteState (.while condition body) with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  dsimp only at seqRun
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    exact nonerror (Prod.mk.inj seqRun).1.symm
  have whileBound := while_compiled_steps condition body context conditionShape bodyShape source middle firstResult
    target firstRun firstNonerror stateRel codeRel excpRel localsRel locs.1
  have sourceCount := controlSteps_seq (.while condition body) tail source
  rw [firstRun] at sourceCount
  have correct : pcCompileCorrectAt (.while condition body) source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetPost,targetRun,_,_,_,resultRel⟩ :=
    correct firstResult middle target context firstRun firstNonerror stateRel codeRel excpRel localsRel locs.1
  rw [compileProgExactHOLW,CrepSteps.steps_seq,targetRun]
  cases firstResult with
  | none =>
    obtain ⟨rfl,_⟩ := resultRel
    simp only
    have tailBound := CrepSteps.branchProgram_static (branch_compile tailShape) targetPost
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
      nlinarith

end SteppedFlapjack.PanToCrepSteps
