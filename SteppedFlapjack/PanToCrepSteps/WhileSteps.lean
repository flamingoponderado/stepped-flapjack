import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.PanToCrepSteps.ControlSteps

/-! Quantitative correctness of Pancake while compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- For a non-error source run, the actual compiled Crep while visits at most
one plus the compiled body size per Pancake control visit. -/
theorem while_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : ScalarExpression context condition) (bodyShape : BranchProgram context body)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.while condition body) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.while condition body)) target ≤
      (1 + sizeOf (compileProgExactHOLW context body)) * controlSteps (.while condition body) source := by
  classical
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result target with
  | _ clock ih =>
    have locs : localisedExpHOL condition = true ∧ localisedProgHOL body = true := by
      simpa [localisedProgHOL] using localised
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have hevalExact : @evalHOLExact width σ _ source.toExact
        (fun address => Classical.propDecidable (source.memaddrs address)) condition =
          some (.val (.word w)) := heval
    obtain ⟨ce,compiled,direct⟩ := scalar_compile conditionShape
    have hce : evalCrepSemHOLExp target ce = some (.word w) := by
      have h := @compileExpValRelHOL width σ _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) context target
        (fun address => Classical.propDecidable (target.memaddrs address))
        condition (.val (.word w)) [ce] .one heval stateRel codeRel localsRel locs.1 compiled
      obtain ⟨values,_,_,_⟩ := h
      simpa [flattenHOL] using values
    have comp : compileProgExactHOLW context (.while condition body) =
        .while ce (compileProgExactHOLW context body) := by
      simp [compileProgExactHOLW,compileWhileExactHOLW,compiled]
    rw [comp,CrepSteps.steps_while]
    simp only [hce]
    have clockRel : source.clock = target.clock := stateRel.2.2.2.2.2.1
    by_cases nz : w ≠ 0
    · by_cases z : source.clock = 0
      · have tz : target.clock = 0 := clockRel ▸ z
        simp only [tz,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero]
        have positive := controlSteps_pos (.while condition body) source
        nlinarith
      · have tz : target.clock ≠ 0 := clockRel ▸ z
        simp only [if_pos (show w ≠ 0 ∧ target.clock ≠ 0 from ⟨nz,tz⟩)]
        rw [if_pos nz,if_neg z] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState body with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyState : panToCrepStateRelFiniteExact source.decClockHOLFinite (decClockCrepSemHOL target) := by
          simpa [panToCrepStateRelFiniteExact,PanSemStateFiniteExact.decClockHOLFinite,decClockCrepSemHOL,clockRel] using stateRel
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyCorrect : pcCompileCorrectAt body source.decClockHOLFinite :=
          (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
        obtain ⟨targetResult,targetPost,targetRun,postState,postCode,postExcp,resultRel⟩ :=
          bodyCorrect bodyResult sourcePost (decClockCrepSemHOL target) context bodyRun bodyNonerror
            bodyState codeRel excpRel localsRel locs.2
        rw [targetRun]
        have bodyBound := CrepSteps.branchProgram_static (branch_compile bodyShape) (decClockCrepSemHOL target)
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [PanSemStateFiniteExact.decClockHOLFinite] at bodyClock
          omega
        have sourceCount := controlSteps_while condition body source
        simp only [hevalExact,if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        have recCase (hres : bodyResult = none ∨ bodyResult = some .continue)
            (hrel : targetResult = none ∨ targetResult = some (.continue 0))
            (postLocals : panToCrepLocalsRelFiniteExact context sourcePost.locals targetPost.locals)
            (tailRun : sourcePost.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal)) :
            1 + (CrepSteps.steps (compileProgExactHOLW context body) (decClockCrepSemHOL target) +
              match (targetResult,targetPost) with
              | (none,t) | (some (.continue 0),t) => CrepSteps.steps (.while ce (compileProgExactHOLW context body)) t
              | _ => 0) ≤
              (1 + sizeOf (compileProgExactHOLW context body)) * controlSteps (.while condition body) source := by
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result targetPost tailRun nonerror
            postState postCode postExcp postLocals rfl
          rw [comp] at recurse
          have counts : controlSteps (.while condition body) source ≥
              1 + controlSteps (.while condition body) sourcePost := by
            rcases hres with h | h <;> simp only [h] at sourceCount <;> rw [sourceCount] <;> simp
          rcases hrel with h | h <;> simp only [h] <;> nlinarith
        cases bodyResult with
        | none =>
          obtain ⟨hresult,hl⟩ := resultRel
          exact recCase (Or.inl rfl) (Or.inl hresult) hl run
        | some r =>
          cases r with
          | «continue» =>
            obtain ⟨hresult,hl⟩ := resultRel
            exact recCase (Or.inr rfl) (Or.inr hresult) hl run
          | error => exact absurd rfl bodyNonerror
          | «break» =>
            obtain ⟨rfl,_⟩ := resultRel
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
          | timeOut =>
            subst resultRel
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
          | returned v =>
            subst resultRel
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
          | finalFfi f =>
            subst resultRel
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
          | exception eid v =>
            simp only [pcCompileCorrectResultRel] at resultRel
            split at resultRel
            · exact resultRel.elim
            obtain ⟨rfl,_⟩ := resultRel
            simp only [Nat.add_zero]
            have positive := controlSteps_pos (.while condition body) source
            nlinarith
    · have tz : ¬ (w ≠ 0 ∧ target.clock ≠ 0) := fun h => nz h.1
      simp only [if_neg tz,Nat.add_zero]
      have positive := controlSteps_pos (.while condition body) source
      nlinarith


/-- Frontend correctness supplies the related Crep run and the quantitative
while bound from the same Pancake execution. -/
theorem while_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : ScalarExpression context condition) (bodyShape : BranchProgram context body)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.while condition body) = true) :
    ∃ ce crepResult crepFinal,
      compileProgExactHOLW context (.while condition body) = .while ce (compileProgExactHOLW context body) ∧
      CrepToLoopSteps.DirectExpression ce ∧
      CrepToLoopSteps.BranchProgram (compileProgExactHOLW context body) ∧
      evalCrepSemHOLProgExact target (compileProgExactHOLW context (.while condition body)) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact sourceFinal crepFinal ∧
      codeRelExactHOLW context sourceFinal.code crepFinal.code ∧
      panToCrepExcpRelFiniteExact context.eids sourceFinal.eshapes ∧
      pcCompileCorrectResultRel context sourceFinal crepFinal result crepResult ∧
      CrepSteps.steps (compileProgExactHOLW context (.while condition body)) target ≤
        (1 + sizeOf (compileProgExactHOLW context body)) * controlSteps (.while condition body) source := by
  obtain ⟨ce,compiled,shape,branch⟩ := while_compile conditionShape bodyShape
  have correct : pcCompileCorrectAt (.while condition body) source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨crepResult,crepFinal,he,hs,hc,hx,hr⟩ :=
    correct result sourceFinal target context run nonerror stateRel codeRel excpRel localsRel localised
  exact ⟨ce,crepResult,crepFinal,compiled,shape,branch,he,hs,hc,hx,hr,
    while_compiled_steps condition body context conditionShape bodyShape source sourceFinal result target
      run nonerror stateRel codeRel excpRel localsRel localised⟩

end SteppedFlapjack.PanToCrepSteps
