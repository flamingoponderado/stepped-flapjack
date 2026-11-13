import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.PanToCrepSteps.FrontendProgram
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel

/-! Quantitative correctness of Pancake while compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- Source evaluation retains the function table across every outcome. -/
theorem source_code_preserved {width : Nat} [NeZero width] {σ : Type}
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ) (r : Option (PanSemResultExact width))
    (run : s.evaluateHOLFiniteState p = (r,t)) : t.code = s.code := by
  have h := evaluateInvariantsHOLFinite p (PanPropsEvalStateFiniteExact.ofPanSemFinite s) r
    (PanPropsEvalStateFiniteExact.ofPanSemFinite t) (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,run])
  exact h.2.2.2.2.2.2.1

/-- For a non-error source run, the actual compiled Crep while visits at most
the body factor per Pancake control visit when that factor is positive. -/
private theorem while_compiled_steps_compositional {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : FrontendScalar context condition)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width))
    (clockLimit : Nat) (bodyFactor : Nat) (factorPositive : 1 ≤ bodyFactor)
    (bodyBound : ∀ (bs bf : PanSemStateFiniteExact width σ) (br : Option (PanSemResultExact width))
      (bt : CrepSemHOLState width σ),
      bs.clock ≤ clockLimit → bs.code = sourceTable →
      bs.evaluateHOLFiniteState body = (br,bf) → br ≠ some .error →
      bt.code = codeTable →
      panToCrepStateRelFiniteExact bs bt → codeRelExactHOLW context bs.code bt.code →
      panToCrepExcpRelFiniteExact context.eids bs.eshapes →
      panToCrepLocalsRelFiniteExact context bs.locals bt.locals → localisedProgHOL body = true →
      CrepSteps.steps (compileProgExactHOLW context body) bt ≤ bodyFactor * controlSteps body bs)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ) (targetTable : target.code = codeTable)
    (sourceLimit : source.clock ≤ clockLimit) (sourceTableEq : source.code = sourceTable)
    (run : source.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals)
    (localised : localisedProgHOL (.while condition body) = true) :
    CrepSteps.steps (compileProgExactHOLW context (.while condition body)) target ≤
      bodyFactor * controlSteps (.while condition body) source := by
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
    obtain ⟨ce,compiled⟩ := frontendScalar_compile conditionShape
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
        have bodyStepBound := bodyBound source.decClockHOLFinite sourcePost bodyResult (decClockCrepSemHOL target)
          (by simp [PanSemStateFiniteExact.decClockHOLFinite]; omega)
          (by simpa [PanSemStateFiniteExact.decClockHOLFinite] using sourceTableEq) bodyRun bodyNonerror (by simpa [decClockCrepSemHOL] using targetTable) bodyState codeRel excpRel localsRel locs.2
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [PanSemStateFiniteExact.decClockHOLFinite] at bodyClock
          omega
        have sourceCount := controlSteps_while condition body source
        simp only [hevalExact,if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        have bodyCount : controlSteps (.while condition body) source ≥
            1 + controlSteps body source.decClockHOLFinite := by
          rw [sourceCount]
          cases bodyResult with
          | none => simp
          | some r => cases r <;> simp
        have recCase (hres : bodyResult = none ∨ bodyResult = some .continue)
            (hrel : targetResult = none ∨ targetResult = some (.continue 0))
            (postLocals : panToCrepLocalsRelFiniteExact context sourcePost.locals targetPost.locals)
            (tailRun : sourcePost.evaluateHOLFiniteState (.while condition body) = (result,sourceFinal)) :
            1 + (CrepSteps.steps (compileProgExactHOLW context body) (decClockCrepSemHOL target) +
              match (targetResult,targetPost) with
              | (none,t) | (some (.continue 0),t) => CrepSteps.steps (.while ce (compileProgExactHOLW context body)) t
              | _ => 0) ≤
              bodyFactor * controlSteps (.while condition body) source := by
          have postTable : targetPost.code = codeTable := by
            have invariant := evaluateCodeInvariantHOL _ _ _ _ targetRun
            exact invariant.trans (by simpa [decClockCrepSemHOL] using targetTable)
          have postSourceTable : sourcePost.code = sourceTable := by
            have invariant := source_code_preserved body source.decClockHOLFinite sourcePost bodyResult bodyRun
            exact invariant.trans (by simpa [PanSemStateFiniteExact.decClockHOLFinite] using sourceTableEq)
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result targetPost postTable (by omega) postSourceTable tailRun nonerror
            postState postCode postExcp postLocals rfl
          rw [comp] at recurse
          have counts : controlSteps (.while condition body) source ≥
              1 + controlSteps body source.decClockHOLFinite + controlSteps (.while condition body) sourcePost := by
            rcases hres with h | h <;> simp only [h] at sourceCount <;>
              rw [sourceCount] <;> simp only [Nat.add_assoc,le_refl]
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


/-- Internal induction predicate: any factor covering the compiled control
weight bounds related executions per source control visit. -/
private def ProgramBound {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (program : ProgHOL width) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat) : Prop :=
  CrepSteps.statementWeight (compileProgExactHOLW context program) ≤ K →
  ∀ {σ : Type} (source sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (target : CrepSemHOLState width σ),
    target.code = codeTable → source.code = sourceTable → source.clock ≤ clockLimit →
    source.evaluateHOLFiniteState program = (result,sourceFinal) → result ≠ some .error →
    panToCrepStateRelFiniteExact source target → codeRelExactHOLW context source.code target.code →
    panToCrepExcpRelFiniteExact context.eids source.eshapes →
    panToCrepLocalsRelFiniteExact context source.locals target.locals →
    CrepSteps.steps (compileProgExactHOLW context program) target ≤
      K * controlSteps program source

/-- Sequence composition for the structural induction. -/
private theorem programBound_seq {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (a b : ProgHOL width) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat)
    (aLocalised : localisedProgHOL a = true) (aBound : ProgramBound context a clockLimit sourceTable codeTable K)
    (bBound : ProgramBound context b clockLimit sourceTable codeTable K) : ProgramBound context (.seq a b) clockLimit sourceTable codeTable K := by
  intro weight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
  have factorPositive : 1 ≤ K := (CrepSteps.statementWeight_pos _).trans weight
  have seqRun := run
  rw [evaluateHOLFiniteState_seq_line780] at seqRun
  rcases firstRun : source.evaluateHOLFiniteState a with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  dsimp only at seqRun
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    exact nonerror (Prod.mk.inj seqRun).1.symm
  have sourceCount := controlSteps_seq a b source
  rw [firstRun] at sourceCount
  have correct : pcCompileCorrectAt a source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetPost,targetRun,postState,postCode,postExcp,resultRel⟩ :=
    correct firstResult middle target context firstRun firstNonerror stateRel codeRel excpRel localsRel
      aLocalised
  have leftSize : CrepSteps.statementWeight (compileProgExactHOLW context a) ≤
      CrepSteps.statementWeight (compileProgExactHOLW context (.seq a b)) := by
    simp only [compileProgExactHOLW]
    simp only [CrepSteps.statementWeight]
    omega
  have rightSize : CrepSteps.statementWeight (compileProgExactHOLW context b) ≤
      CrepSteps.statementWeight (compileProgExactHOLW context (.seq a b)) := by
    simp only [compileProgExactHOLW]
    simp only [CrepSteps.statementWeight]
    omega
  have firstBound' := aBound (leftSize.trans weight) source middle firstResult target targetTable sourceTableEq sourceLimit firstRun firstNonerror stateRel codeRel excpRel localsRel
  rw [compileProgExactHOLW,CrepSteps.steps_seq,targetRun]
  cases firstResult with
  | none =>
    obtain ⟨rfl,postLocals⟩ := resultRel
    simp only
    have postTable : targetPost.code = codeTable := (evaluateCodeInvariantHOL _ _ _ _ targetRun).trans targetTable
    have middleTable : middle.code = sourceTable := (source_code_preserved a source middle none firstRun).trans sourceTableEq
    have middleLimit : middle.clock ≤ clockLimit := (evaluateHOLFiniteState_clock_le_result source a _ middle firstRun).trans sourceLimit
    have secondBound' := bBound (rightSize.trans weight) middle sourceFinal result targetPost postTable middleTable middleLimit seqRun nonerror postState postCode postExcp postLocals
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


/-- Loop composition for the structural induction. -/
private theorem programBound_while {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : ExpHOL width) (body : ProgHOL width) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat)
    (conditionShape : FrontendScalar context condition) (bodyLocalised : localisedProgHOL body = true)
    (bodyBound : ProgramBound context body clockLimit sourceTable codeTable K) : ProgramBound context (.while condition body) clockLimit sourceTable codeTable K := by
  intro weight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
  have localised : localisedProgHOL (.while condition body) = true := by
    simp [localisedProgHOL,frontendScalar_localised conditionShape,bodyLocalised]
  obtain ⟨ce,compiled⟩ := frontendWhile_compile context condition body conditionShape
  have sizeBound : CrepSteps.statementWeight (compileProgExactHOLW context body) ≤ K := by
    rw [compiled] at weight
    simp only [CrepSteps.statementWeight] at weight
    omega
  have positive : 1 ≤ K := (CrepSteps.statementWeight_pos _).trans sizeBound
  have bounded := while_compiled_steps_compositional condition body context conditionShape
    sourceTable codeTable clockLimit K positive (by
      intro bs bf br bt hlimit hsTable hrun hgood htable hstate hcode hexcp hlocals _
      exact bodyBound sizeBound bs bf br bt htable hsTable hlimit hrun hgood hstate hcode hexcp hlocals)
    source sourceFinal result target targetTable sourceLimit sourceTableEq run nonerror stateRel codeRel excpRel localsRel localised
  exact bounded


/-- Conditional composition for the structural induction. -/
private theorem programBound_ite {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : ExpHOL width) (a b : ProgHOL width) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat)
    (conditionShape : FrontendScalar context condition)
    (aBound : ProgramBound context a clockLimit sourceTable codeTable K) (bBound : ProgramBound context b clockLimit sourceTable codeTable K) :
    ProgramBound context (.ite condition a b) clockLimit sourceTable codeTable K := by
  classical
  intro weight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
  have factorPositive : 1 ≤ K := (CrepSteps.statementWeight_pos _).trans weight
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  obtain ⟨ce,compiled⟩ := frontendScalar_compile conditionShape
  have hce : evalCrepSemHOLExp target ce = some (.word w) := by
    have h := @compileExpValRelHOL width σ _ source
      (fun address => Classical.propDecidable (source.memaddrs address)) context target
      (fun address => Classical.propDecidable (target.memaddrs address))
      condition (.val (.word w)) [ce] .one heval stateRel codeRel localsRel
      (frontendScalar_localised conditionShape) compiled
    obtain ⟨values,_,_,_⟩ := h
    simpa [flattenHOL] using values
  have comp : compileProgExactHOLW context (.ite condition a b) =
      .ite ce (compileProgExactHOLW context a) (compileProgExactHOLW context b) := by
    simp [compileProgExactHOLW,compileIfExactHOLW,compiled]
  have leftSize : CrepSteps.statementWeight (compileProgExactHOLW context a) ≤
      CrepSteps.statementWeight (compileProgExactHOLW context (.ite condition a b)) := by
    rw [comp]; simp only [CrepSteps.statementWeight]; omega
  have rightSize : CrepSteps.statementWeight (compileProgExactHOLW context b) ≤
      CrepSteps.statementWeight (compileProgExactHOLW context (.ite condition a b)) := by
    rw [comp]; simp only [CrepSteps.statementWeight]; omega
  have sourceCount := controlSteps_ite condition a b source
  simp only [heval] at sourceCount
  rw [comp,CrepSteps.steps_ite,hce]
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false] at sourceCount ⊢
    have scaled := bBound (rightSize.trans weight) source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
    nlinarith
  · simp only [if_neg zero] at run
    simp only [if_pos zero] at sourceCount ⊢
    have scaled := aBound (leftSize.trans weight) source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
    nlinarith


/-- Declaration composition for the structural induction. -/
private theorem programBound_decl {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) (initializer : ExpHOL width) (body : ProgHOL width) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat)
    (initializerShape : FrontendScalar context initializer)
    (bodyBound : ProgramBound (scalarDeclContext context name) body clockLimit sourceTable codeTable K) :
    ProgramBound context (.dec name .one initializer body) clockLimit sourceTable codeTable K := by
  classical
  intro weight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
  have factorPositive : 1 ≤ K := (CrepSteps.statementWeight_pos _).trans weight
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases heval : @evalHOLExact width σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) initializer with
  | none =>
    rw [heval] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    rw [heval] at run
    dsimp only at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · rw [if_pos valid] at run
      have shape := (shapeEqHOL_eq_true _ _).mp valid
      cases value with
      | val word =>
        rcases bodyRun : (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source).evaluateHOLFiniteState body with ⟨bodyResult,bodyFinal⟩
        rw [bodyRun] at run
        have sameResult : bodyResult = result := (Prod.mk.inj run).1
        subst result
        obtain ⟨ce,compiled⟩ := frontendScalar_compile initializerShape
        have hce : evalCrepSemHOLExp target ce = some word := by
          have h := @compileExpValRelHOL width σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) context target
            (fun address => Classical.propDecidable (target.memaddrs address))
            initializer (.val word) [ce] .one heval stateRel codeRel localsRel
            (frontendScalar_localised initializerShape) compiled
          obtain ⟨values,_,_,_⟩ := h
          simpa [flattenHOL] using values
        have innerLocals := localsRelExtendNewVarHOL context source.locals target.locals
          (.val word) name [context.vmax+1] (by
            refine ⟨localsRel, ?_, ?_, ?_, ?_⟩ <;> simp [shapeOfHOLExact])
        have innerState : panToCrepStateRelFiniteExact
            (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source)
            (CrepSemHOLState.setVar (context.vmax+1) word target) := by
          simpa [panToCrepStateRelFiniteExact,PanSemStateFiniteExact.setVarHOLFinite,
            CrepSemHOLState.setVar] using stateRel
        have singletonUpdate : target.locals.updateListEq [(context.vmax+1,word)] =
            target.locals.updateEq (context.vmax+1,word) := by
          apply HolFiniteMapExact.ext
          funext k
          rfl
        have innerLocals' : panToCrepLocalsRelFiniteExact (scalarDeclContext context name)
            (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source).locals
            (CrepSemHOLState.setVar (context.vmax+1) word target).locals := by
          simpa [scalarDeclContext,PanSemStateFiniteExact.setVarHOLFinite,CrepSemHOLState.setVar,
            shapeOfHOLExact,Flapjack.Pancake.PanLang.sizeOfShapeHOL,flattenHOL,singletonUpdate] using innerLocals
        have count := controlSteps_dec name .one initializer body source (.val word) heval
          (by simp [shapeEqHOL,shapeOfHOLExact])
        obtain ⟨compiledValue,comp⟩ := frontendDecl_compile context name initializer body initializerShape
        have valueEq : compiledValue = ce := by
          simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext] at comp
          exact comp.symm
        subst compiledValue
        have sizeBound : 1 + CrepSteps.statementWeight (compileProgExactHOLW (scalarDeclContext context name) body) ≤
            CrepSteps.statementWeight (compileProgExactHOLW context (.dec name .one initializer body)) := by
          rw [comp]
          simp only [CrepSteps.statementWeight]
          omega
        have childSize : CrepSteps.statementWeight (compileProgExactHOLW (scalarDeclContext context name) body) ≤
            CrepSteps.statementWeight (compileProgExactHOLW context (.dec name .one initializer body)) := by omega
        have bound := bodyBound (childSize.trans weight) _ bodyFinal bodyResult _ (by simpa [CrepSemHOLState.setVar] using targetTable) (by simpa [PanSemStateFiniteExact.setVarHOLFinite] using sourceTableEq) (by simpa [PanSemStateFiniteExact.setVarHOLFinite] using sourceLimit) bodyRun nonerror innerState
          (by simpa [codeRelExactHOLW,scalarDeclContext,PanSemStateFiniteExact.setVarHOLFinite,CrepSemHOLState.setVar] using codeRel)
          (by simpa [scalarDeclContext,PanSemStateFiniteExact.setVarHOLFinite] using excpRel) innerLocals'
        have scaled := bound
        rw [comp,CrepSteps.steps_dec,hce,count]
        nlinarith
      | rStruct fields => simp [shapeOfHOLExact] at shape
      | nStruct name fields => simp [shapeOfHOLExact] at shape
    · rw [if_neg valid] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror


/-- Loop-free programs are the base cases of the structural induction. -/
private theorem programBound_static {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {program : ProgHOL width}
    (shape : FrontendProgram context program) (loopFree : noWhile program = true) (clockLimit : Nat)
    (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (codeTable : HolFiniteMapExact MlS (List Nat × CrepProgHOL width)) (K : Nat) :
    ProgramBound context program clockLimit sourceTable codeTable K := by
  intro weight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
  have static := CrepSteps.staticProgram_statementWeight (frontendLoopFree_static shape loopFree) target
  have positive := controlSteps_pos program source
  nlinarith

private theorem frontendProgramBound {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {program : ProgHOL width}
    (shape : FrontendProgram context program) : ∀ clockLimit sourceTable codeTable K, ProgramBound context program clockLimit sourceTable codeTable K := by
  induction shape with
  | skip => intro n st t k; exact programBound_static .skip rfl n st t k
  | «break» => intro n st t k; exact programBound_static .break rfl n st t k
  | «continue» => intro n st t k; exact programBound_static .continue rfl n st t k
  | tick => intro n st t k; exact programBound_static .tick rfl n st t k
  | storeStruct a fields => intro n st t k; exact programBound_static (.storeStruct a fields) rfl n st t k
  | store a v => intro n st t k; exact programBound_static (.store a v) rfl n st t k
  | assign reg found e => intro n st t k; exact programBound_static (.assign reg found e) rfl n st t k
  | decl e body ih => intro n st t k; exact programBound_decl _ _ _ _ n st t k e (ih n st t k)
  | seq a b iha ihb => intro n st t k; exact programBound_seq _ _ _ n st t k (frontendProgram_localised a) (iha n st t k) (ihb n st t k)
  | ite condition a b iha ihb => intro n st t k; exact programBound_ite _ _ _ _ n st t k condition (iha n st t k) (ihb n st t k)
  | «while» condition body ih => intro n st t k; exact programBound_while _ _ _ n st t k condition (frontendProgram_localised body) (ih n st t k)
  | ret e => intro n st t k; exact programBound_static (.ret e) rfl n st t k

/-- Every generalized frontend program has a Crep visit bound computed only
from its generated code and its actual source control visits. -/
theorem frontend_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (context : PanToCrepContextExact width) (program : ProgHOL width)
    (shape : FrontendProgram context program)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ)
    (run : source.evaluateHOLFiniteState program = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals) :
    CrepSteps.steps (compileProgExactHOLW context program) target ≤
      CrepSteps.statementWeight (compileProgExactHOLW context program) * controlSteps program source := by
  exact frontendProgramBound shape source.clock source.code target.code _ (Nat.le_refl _) source sourceFinal result target rfl rfl (Nat.le_refl _) run nonerror stateRel codeRel excpRel localsRel


/-- A frontend run has a corresponding Crep run with a code-derived visit
bound. The source budget bounds the exact source control-visit measure. -/
theorem frontend_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (context : PanToCrepContextExact width) (program : ProgHOL width)
    (shape : FrontendProgram context program)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ) (sourceLimit : Nat)
    (run : source.evaluateHOLFiniteState program = (result,sourceFinal))
    (nonerror : result ≠ some .error) (sourceBound : controlSteps program source ≤ sourceLimit)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW context source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact context.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact context source.locals target.locals) :
    ∃ targetResult targetFinal,
      evalCrepSemHOLProgExact target (compileProgExactHOLW context program) = (targetResult,targetFinal) ∧
      panToCrepStateRelFiniteExact sourceFinal targetFinal ∧
      codeRelExactHOLW context sourceFinal.code targetFinal.code ∧
      panToCrepExcpRelFiniteExact context.eids sourceFinal.eshapes ∧
      pcCompileCorrectResultRel context sourceFinal targetFinal result targetResult ∧
      CrepSteps.steps (compileProgExactHOLW context program) target ≤
        CrepSteps.statementWeight (compileProgExactHOLW context program) * sourceLimit := by
  have correct : pcCompileCorrectAt program source :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetFinal,targetRun,finalRel,finalCode,finalExcp,resultRel⟩ :=
    correct result sourceFinal target context run nonerror stateRel codeRel excpRel localsRel
      (frontendProgram_localised shape)
  refine ⟨targetResult,targetFinal,targetRun,finalRel,finalCode,finalExcp,resultRel,?_⟩
  exact (frontend_compiled_steps context program shape source sourceFinal result target run nonerror
    stateRel codeRel excpRel localsRel).trans (Nat.mul_le_mul_left _ sourceBound)


/-- The static-body case is an instance of compositional loop induction. -/
theorem while_compiled_steps_general {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : FrontendScalar context condition)
    (bodyShape : CrepSteps.StaticProgram (compileProgExactHOLW context body))
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
  apply while_compiled_steps_compositional condition body context conditionShape
    source.code target.code source.clock (1 + sizeOf (compileProgExactHOLW context body)) (by omega) ?_ source sourceFinal result target rfl (Nat.le_refl _) rfl
    run nonerror stateRel codeRel excpRel localsRel localised
  intro bs bf br bt _ _ _ _ _ _ _ _ _ _
  have static := CrepSteps.staticProgram_steps bodyShape bt
  have positive := controlSteps_pos body bs
  nlinarith


/-- The direct-expression special case reuses the generalized while bound. -/
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
  exact while_compiled_steps_general condition body context (frontendScalar_of_direct conditionShape)
    (CrepSteps.branchProgram_staticShape (branch_compile bodyShape)) source sourceFinal result target
    run nonerror stateRel codeRel excpRel localsRel localised


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

/-- A reached source tail call and its compiled call visit the corresponding
callee entries, with the compiler relations preserved at those entries. -/
theorem tailCall_entries {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (fname : MlS) (argexps : List (ExpHOL width))
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true) :
    ∃ shapes : List (MlS × ShapeHOL),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      let sourceEntry := PanSemStateFiniteExact.callEntryStateHOLFinite source locals
      let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
      source.code.lookup fname = some (shapes,body,rsh) ∧
      localisedProgHOL body = true ∧
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) ∧
      controlSteps (.call none fname argexps) source = 1 + controlSteps body sourceEntry ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.call none fname argexps)) target =
        1 + CrepSteps.steps (compileProgExactHOLW next body) targetEntry ∧
      panToCrepStateRelFiniteExact sourceEntry targetEntry ∧
      codeRelExactHOLW next sourceEntry.code targetEntry.code ∧
      panToCrepExcpRelFiniteExact next.eids sourceEntry.eshapes ∧
      panToCrepLocalsRelFiniteExact next sourceEntry.locals targetEntry.locals := by
  obtain ⟨shapes, hsrc, hbodyLocal, _, hlen, htargs, htlookup, hs, hc, he, hl⟩ :=
    pcCompileCorrectCallPrelude source target ctxt fname argexps args body locals rsh hargs found stateRel codeRel excpRel localsRel localised
  let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
  let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
  have htgt := (codeRelExactHOLW_imp ctxt source.code target.code codeRel fname shapes body rsh hsrc).2.2
  have targetClock : target.clock ≠ 0 := by rw [← stateRel.2.2.2.2.2.1]; exact clock
  have localsEq : tlcHOL ns args = HolFiniteMapExact.empty.updateList (ns.zip (args.flatMap flattenHOL)) := by
    simp only [lookupCodeFiniteHOL, htgt, hlen, List.nodup_range, and_self, if_true, Option.some.injEq,
      Prod.mk.injEq, true_and] at htlookup
    exact htlookup.symm
  have count := CrepSteps.steps_call_tail fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst) target
    (args.flatMap flattenHOL) ns (compileProgExactHOLW next body) htargs htgt hlen List.nodup_range targetClock
  refine ⟨shapes,hsrc,hbodyLocal,htgt,controlSteps_tailCall fname argexps source args body locals rsh hargs found clock, ?_,hs,hc,he,hl⟩
  dsimp [next,ns] at count localsEq
  rw [localsEq]
  simpa [compileProgExactHOLW,compileCallNoReturnExactHOLW,decClockCrepSemHOL] using count

private theorem nestedDecs_zero_steps {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (body : CrepProgHOL width) (s : CrepSemHOLState width σ) :
    CrepSteps.steps (nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body) s =
      names.length + CrepSteps.steps body (names.foldl (fun st name => CrepSemHOLState.setVar name (.word 0) st) s) := by
  induction names generalizing s with
  | nil => simp [nestedDecsHOL]
  | cons name rest ih =>
    simp only [List.length_cons,List.replicate_succ,nestedDecsHOL,CrepSteps.steps_dec,evalCrepSemHOLExp,List.foldl_cons]
    rw [ih]
    omega

private theorem zeroInit_eq {width : Nat} [NeZero width] {σ : Type} (names : List Nat) (s : CrepSemHOLState width σ) :
    names.foldl (fun st name => CrepSemHOLState.setVar name (.word 0) st) s =
      {s with locals := s.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))} := by
  induction names generalizing s with
  | nil => simp [HolFiniteMapExact.updateListEq, FUPDATE_LIST_HOL]
  | cons n ns ih =>
    simp only [List.foldl_cons,List.length_cons,List.replicate_succ,List.zip_cons_cons]
    rw [ih]
    simp [CrepSemHOLState.setVar,HolFiniteMapExact.updateListEq,HolFiniteMapExact.updateEq,FUPDATE_LIST_HOL_cons]

/-- The generated return slots and selected continuation contribute their exact
Crep visits to a declaration call. -/
theorem decCall_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (args : List (ExpHOL width)) (continuation : ProgHOL width) (target : CrepSemHOLState width σ) :
    let names := decCallSlots ctxt shape
    let pre := {target with locals := target.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))}
    let call : CrepProgHOL width := .call (some (names,none)) fname ((compileExpExactHOLWList ctxt args).flatMap Prod.fst)
    let cont := compileProgExactHOLW (decCallCtxt ctxt name shape) continuation
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname args continuation)) target =
      names.length + (1 + CrepSteps.steps call pre + match evalCrepSemHOLProgExact pre call with
        | (none,post) => CrepSteps.steps cont post
        | _ => 0) := by
  rw [compileDecCallShape,nestedDecs_zero_steps,zeroInit_eq,CrepSteps.steps_seq]
  rfl

/-- Return-slot initialization preserves the corresponding callee entries. -/
theorem decCall_entries {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (fname : MlS) (shape : ShapeHOL) (argexps : List (ExpHOL width))
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true) :
    ∃ shapes : List (MlS × ShapeHOL),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      let pre := {target with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip
        (List.replicate (decCallSlots ctxt shape).length (.word 0)))}
      let sourceEntry := PanSemStateFiniteExact.callEntryStateHOLFinite source locals
      let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
      source.code.lookup fname = some (shapes,body,rsh) ∧
      localisedProgHOL body = true ∧
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) ∧
      CrepSteps.steps (.call (some (decCallSlots ctxt shape,none)) fname
          ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst)) pre =
        1 + CrepSteps.steps (compileProgExactHOLW next body) targetEntry ∧
      panToCrepStateRelFiniteExact sourceEntry targetEntry ∧
      codeRelExactHOLW next sourceEntry.code targetEntry.code ∧
      panToCrepExcpRelFiniteExact next.eids sourceEntry.eshapes ∧
      panToCrepLocalsRelFiniteExact next sourceEntry.locals targetEntry.locals := by
  classical
  obtain ⟨shapes, hsrc, hbodyLocal, _, hlen, htargs, htlookup, hs, hc, he, hl⟩ :=
    pcCompileCorrectCallPrelude source target ctxt fname argexps args body locals rsh hargs found stateRel codeRel excpRel localsRel localised
  let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
  let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
  have htgt := (codeRelExactHOLW_imp ctxt source.code target.code codeRel fname shapes body rsh hsrc).2.2
  have targetClock : target.clock ≠ 0 := by rw [← stateRel.2.2.2.2.2.1]; exact clock
  have localsEq : tlcHOL ns args = HolFiniteMapExact.empty.updateList (ns.zip (args.flatMap flattenHOL)) := by
    simp only [lookupCodeFiniteHOL, htgt, hlen, List.nodup_range, and_self, if_true, Option.some.injEq,
      Prod.mk.injEq, true_and] at htlookup
    exact htlookup.symm
  let slots := decCallSlots ctxt shape
  let zeros := List.replicate slots.length (HolWordLab.word (0 : BitVec width))
  let pre : CrepSemHOLState width σ := {target with locals := target.locals.updateListEq (slots.zip zeros)}
  have distinct : distinctListsHol slots (((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst).flatMap crepExpVarsHOL) = true := by
    exact pcCompileCorrectCallRetSlotsDistinct ctxt argexps (sizeOfShapeHOL shape) localsRel.2.1
  have targetArgs : ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst).mapM
      (@evalCrepSemHOLExp width _ σ pre) = some (args.flatMap flattenHOL) := by
    apply optMmapEvalDistinctListsNotAffectHOL _ target _ slots zeros
    exact ⟨htargs,by simp [zeros],distinct⟩
  have targetFound : pre.code.lookup fname = some (ns,compileProgExactHOLW next body) := htgt
  have count := CrepSteps.steps_call_returning slots fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst) pre
    (args.flatMap flattenHOL) ns (compileProgExactHOLW next body) targetArgs targetFound hlen List.nodup_range
    (decCallSlots_nodup ctxt shape) targetClock
  refine ⟨shapes,hsrc,hbodyLocal,htgt,?_,hs,hc,he,hl⟩
  dsimp [next,ns,pre,slots,zeros] at count localsEq
  rw [localsEq]
  simpa [decClockCrepSemHOL] using count


private theorem nestedDecs_weight {width : Nat} [NeZero width]
    (names : List Nat) (body : CrepProgHOL width) :
    CrepSteps.statementWeight (nestedDecsHOL names (List.replicate names.length (.const (0 : BitVec width))) body) =
      names.length + CrepSteps.statementWeight body := by
  induction names with
  | nil => simp [nestedDecsHOL]
  | cons name rest ih =>
    simp only [List.length_cons,List.replicate_succ,nestedDecsHOL,CrepSteps.statementWeight,ih]
    omega

/-- The actual generated statement weight includes every return slot, the call,
and the continuation. -/
theorem decCall_statementWeight {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (args : List (ExpHOL width)) (cont : ProgHOL width) :
    CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname args cont)) =
      sizeOfShapeHOL shape + 2 + CrepSteps.statementWeight (compileProgExactHOLW (decCallCtxt ctxt name shape) cont) := by
  rw [compileDecCallShape,nestedDecs_weight]
  simp [decCallSlots,CrepSteps.statementWeight,Nat.add_assoc]

/-- Slot initialization preserves the call arguments and callee execution. -/
theorem initializedCall_afterBody {width : Nat} [NeZero width] {σ : Type}
    (target : CrepSemHOLState width σ) (fname : MlS) (args : List (CrepExpHOL width))
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width)) (names : List Nat)
    (hargs : args.mapM (evalCrepSemHOLExp target) = some flat)
    (found : lookupCodeFiniteHOL target.code fname flat flat.length = some (body,locals))
    (clock : target.clock ≠ 0) (distinct : names.Nodup)
    (disjoint : distinctListsHol names (args.flatMap crepExpVarsHOL) = true) :
    let pre := {target with locals := target.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))}
    evalCrepSemHOLProgExact pre (.call (some (names,none)) fname args) =
      crepCallAfterBody pre (some (names,none))
        (evalCrepSemHOLProgExact {decClockCrepSemHOL target with locals := locals} body) := by
  classical
  let zeros := List.replicate names.length (HolWordLab.word (0 : BitVec width))
  let pre : CrepSemHOLState width σ := {target with locals := target.locals.updateListEq (names.zip zeros)}
  have argsPre : args.mapM (evalCrepSemHOLExp pre) = some flat := by
    apply optMmapEvalDistinctListsNotAffectHOL args target flat names zeros
    exact ⟨hargs,by simp [zeros],disjoint⟩
  have guard : ∀ rts h, (some (names,none) : Option (List Nat × Option (BitVec width × CrepProgHOL width))) = some (rts,h) → rts.Nodup := by
    intro rts h eq
    cases eq
    exact distinct
  exact crepCallTarget pre (some (names,none)) fname args flat body locals argsPre found guard clock


/-- A successful call installs the returned values in its initialized slots. -/
theorem initializedCall_return {width : Nat} [NeZero width] {σ : Type}
    (target : CrepSemHOLState width σ) (fname : MlS) (args : List (CrepExpHOL width))
    (flat returned : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width)) (names : List Nat)
    (post : CrepSemHOLState width σ)
    (hargs : args.mapM (evalCrepSemHOLExp target) = some flat)
    (found : lookupCodeFiniteHOL target.code fname flat flat.length = some (body,locals))
    (clock : target.clock ≠ 0) (distinct : names.Nodup)
    (disjoint : distinctListsHol names (args.flatMap crepExpVarsHOL) = true)
    (bodyRun : evalCrepSemHOLProgExact {decClockCrepSemHOL target with locals := locals} body =
      (some (.return returned),post)) (arity : returned.length = names.length) :
    let pre := {target with locals := target.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))}
    evalCrepSemHOLProgExact pre (.call (some (names,none)) fname args) =
      (none,{post with locals := target.locals.updateListEq (names.zip returned)}) := by
  let zeros := List.replicate names.length (HolWordLab.word (0 : BitVec width))
  let pre : CrepSemHOLState width σ := {target with locals := target.locals.updateListEq (names.zip zeros)}
  have call := initializedCall_afterBody target fname args flat body locals names hargs found clock distinct disjoint
  rw [bodyRun] at call
  simp only [crepCallAfterBody] at call
  rw [if_neg (by rw [arity]; exact fun h => h rfl)] at call
  have hzlen : names.length = zeros.length := by simp [zeros]
  rw [mapM_lookup_updateListEq _ _ _ distinct hzlen] at call
  dsimp only at call
  rw [updateListEq_overwrite target.locals _ _ _ hzlen arity.symm] at call
  exact call

/-- A non-returning callee cannot reach the normal continuation. -/
theorem initializedCall_terminal {width : Nat} [NeZero width] {σ : Type}
    (target : CrepSemHOLState width σ) (fname : MlS) (args : List (CrepExpHOL width))
    (flat : List (HolWordLab width)) (body : CrepProgHOL width)
    (locals : HolFiniteMapExact Nat (HolWordLab width)) (names : List Nat)
    (out : Option (CrepResultHOLExact width)) (post : CrepSemHOLState width σ)
    (hargs : args.mapM (evalCrepSemHOLExp target) = some flat)
    (found : lookupCodeFiniteHOL target.code fname flat flat.length = some (body,locals))
    (clock : target.clock ≠ 0) (distinct : names.Nodup)
    (disjoint : distinctListsHol names (args.flatMap crepExpVarsHOL) = true)
    (bodyRun : evalCrepSemHOLProgExact {decClockCrepSemHOL target with locals := locals} body = (out,post))
    (terminal : ∀ returned, out ≠ some (.return returned)) :
    let pre := {target with locals := target.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))}
    (evalCrepSemHOLProgExact pre (.call (some (names,none)) fname args)).1 ≠ none := by
  have call := initializedCall_afterBody target fname args flat body locals names hargs found clock distinct disjoint
  rw [bodyRun] at call
  dsimp only at call ⊢
  rw [call]
  cases out with
  | none => simp [crepCallAfterBody]
  | some r => cases r <;> simp_all [crepCallAfterBody]

/-- A well-shaped returned value restores the compiler relations for the
declaration-call continuation. -/
theorem decCall_continuation_relations {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name : MlS) (shape : ShapeHOL)
    (source sourcePost : PanSemStateFiniteExact width σ) (target targetPost : CrepSemHOLState width σ)
    (value : ValueHOL width)
    (stateRel : panToCrepStateRelFiniteExact sourcePost targetPost)
    (codeRel : codeRelExactHOLW ctxt sourcePost.code targetPost.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids sourcePost.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (valid : shapeOfHOLExact value = shape)
    (wf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true) :
    let sourceCont := PanSemStateFiniteExact.setVarHOLFinite name value {sourcePost with locals := source.locals}
    let targetCont := {targetPost with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL value))}
    panToCrepStateRelFiniteExact sourceCont targetCont ∧
    codeRelExactHOLW (decCallCtxt ctxt name shape) sourceCont.code targetCont.code ∧
    panToCrepExcpRelFiniteExact (decCallCtxt ctxt name shape).eids sourceCont.eshapes ∧
    panToCrepLocalsRelFiniteExact (decCallCtxt ctxt name shape) sourceCont.locals targetCont.locals := by
  have length := flattenHOL_length_eq_sizeOfShapeHOL value wf
  have hlen : (flattenHOL value).length = (decCallSlots ctxt shape).length := by
    simp [decCallSlots,length,valid]
  have loc := localsRelExtendNewVarHOL ctxt source.locals target.locals value name
    (decCallSlots ctxt shape)
    ⟨localsRel, wf, decCallSlots_nodup ctxt shape, fun y hy => by
      have := decCallSlots_gt ctxt shape y hy
      rw [valid]
      exact this, by rw [← hlen,length]⟩
  rw [valid] at loc
  refine ⟨?_,?_,?_,?_⟩
  · simpa [panToCrepStateRelFiniteExact,PanSemStateFiniteExact.setVarHOLFinite] using stateRel
  · simpa [decCallCtxt,PanSemStateFiniteExact.setVarHOLFinite,codeRelExactHOLW] using codeRel
  · simpa [decCallCtxt,PanSemStateFiniteExact.setVarHOLFinite] using excpRel
  · exact loc

open Flapjack.PanSemStateFiniteExact in
/-- A successful declaration call exposes exact source and Crep visits and
the related continuation states, with no assumed callee simulation. -/
theorem decCall_return_bridge {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (value : ValueHOL width) (sourcePost : PanSemStateFiniteExact width σ)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (some (.returned value),sourcePost))
    (valid : shapeOfHOLExact value = shape) (returnValid : shapeOfHOLExact value = rsh) :
    ∃ shapes : List (MlS × ShapeHOL), ∃ targetPost : CrepSemHOLState width σ,
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      let sourceEntry := callEntryStateHOLFinite source locals
      let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
      let sourceCont := setVarHOLFinite name value {sourcePost with locals := source.locals}
      let targetCont := {targetPost with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL value))}
      source.code.lookup fname = some (shapes,body,rsh) ∧
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) ∧
      localisedProgHOL body = true ∧
      panToCrepStateRelFiniteExact sourceEntry targetEntry ∧
      codeRelExactHOLW next sourceEntry.code targetEntry.code ∧
      panToCrepExcpRelFiniteExact next.eids sourceEntry.eshapes ∧
      panToCrepLocalsRelFiniteExact next sourceEntry.locals targetEntry.locals ∧
      evalCrepSemHOLProgExact targetEntry (compileProgExactHOLW next body) = (some (.return (flattenHOL value)),targetPost) ∧
      targetPost.code = target.code ∧
      sourcePost.code = source.code ∧
      sourcePost.clock < source.clock ∧
      controlSteps (.decCall name shape fname argexps continuation) source =
        1 + controlSteps body sourceEntry + controlSteps continuation sourceCont ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target =
        (decCallSlots ctxt shape).length + 2 + CrepSteps.steps (compileProgExactHOLW next body) targetEntry +
          CrepSteps.steps (compileProgExactHOLW (decCallCtxt ctxt name shape) continuation) targetCont ∧
      panToCrepStateRelFiniteExact sourceCont targetCont ∧
      codeRelExactHOLW (decCallCtxt ctxt name shape) sourceCont.code targetCont.code ∧
      panToCrepExcpRelFiniteExact (decCallCtxt ctxt name shape).eids sourceCont.eshapes ∧
      panToCrepLocalsRelFiniteExact (decCallCtxt ctxt name shape) sourceCont.locals targetCont.locals := by
  classical
  have wfValue : isWfShapeValueHOLExact [] value = true := by
    have h := panToCrepFiniteEvaluateShapeInvariantRetInst2 argexps source fname args body
      locals rsh body (.returned value) sourcePost target ctxt target.locals
      (by simpa [evalListHOLFiniteClassical] using hargs)
      (PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some _ _ _ _ _ _ found) bodyRun stateRel localsRel
    simpa using h
  have wf : isWfShapeExactHOL ([] : StructContextExact) (shapeOfHOLExact value) = true := by
    rw [isWfShapeExactHOL_shapeOfHOLExact_eq_isWfShapeValueHOLExact_nil [] rfl value]
    exact wfValue
  obtain ⟨shapes,hsrc,hbodyLocal,htgt,callCount,hs,hc,he,hl⟩ :=
    decCall_entries ctxt fname shape argexps source target args body locals rsh hargs found clock stateRel codeRel excpRel localsRel localised
  let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
  let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
  let entry := callEntryStateHOLFinite source locals
  let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
  have correct : pcCompileCorrectAt body entry := (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨result,targetPost,targetRun,postState,postCode,postExcp,resultRel⟩ :=
    correct (some (.returned value)) sourcePost targetEntry next bodyRun (by simp) hs hc he hl hbodyLocal
  simp only [pcCompileCorrectResultRel] at resultRel
  subst result
  have ccode : codeRelExactHOLW ctxt sourcePost.code targetPost.code :=
    codeRelExactHOLW_ctxtFc ctxt _ _ _ _ _ postCode
  have continuations := decCall_continuation_relations ctxt name shape source sourcePost target targetPost value postState ccode postExcp localsRel valid wf
  have ⟨shapes2,hsrc2,_,_,_,htargs,htlookup,_,_,_,_⟩ :=
    pcCompileCorrectCallPrelude source target ctxt fname argexps args body locals rsh hargs found stateRel codeRel excpRel localsRel localised
  have shapesEq : shapes2 = shapes := by rw [hsrc] at hsrc2; exact (congrArg Prod.fst (Option.some.inj hsrc2)).symm
  subst shapes2
  have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt argexps (sizeOfShapeHOL shape) localsRel.2.1
  have targetClock : target.clock ≠ 0 := by rw [← stateRel.2.2.2.2.2.1]; exact clock
  have len : (flattenHOL value).length = (decCallSlots ctxt shape).length := by
    simp [decCallSlots,flattenHOL_length_eq_sizeOfShapeHOL value wf,valid]
  have callRun := initializedCall_return target fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst)
    (args.flatMap flattenHOL) (flattenHOL value) (compileProgExactHOLW next body) (tlcHOL ns args)
    (decCallSlots ctxt shape) targetPost htargs htlookup targetClock (decCallSlots_nodup ctxt shape) hdist targetRun len
  have fix : fixClockHOLFinite entry (some (PanSemResultExact.returned value),sourcePost) = (some (PanSemResultExact.returned value),sourcePost) := by
    rw [← bodyRun,fixClockHOLFinite_evaluate]
  have sourceCount := controlSteps_decCall_return name fname shape argexps continuation source args body locals rsh value sourcePost
    hargs found clock bodyRun ((shapeEqHOL_eq_true _ _).mpr valid) ((shapeEqHOL_eq_true _ _).mpr returnValid)
  dsimp only at sourceCount
  change fixClockHOLFinite (callEntryStateHOLFinite source locals) (some (PanSemResultExact.returned value),sourcePost) = _ at fix
  rw [fix] at sourceCount
  have targetCount := decCall_compiled_steps ctxt name fname shape argexps continuation target
  dsimp only at targetCount
  rw [callCount,callRun] at targetCount
  simp only at targetCount
  have targetCode : targetPost.code = target.code := by
    have h := evaluateCodeInvariantHOL _ _ _ _ targetRun
    simpa [targetEntry,decClockCrepSemHOL] using h
  have sourceCode : sourcePost.code = source.code := by
    have h := source_code_preserved body entry sourcePost (some (.returned value)) bodyRun
    simpa [entry,callEntryStateHOLFinite] using h
  have sourceClock : sourcePost.clock < source.clock := by
    have h := evaluateHOLFiniteState_clock_le_result entry body _ sourcePost bodyRun
    simp only [entry,callEntryStateHOLFinite] at h
    omega
  refine ⟨shapes,targetPost,hsrc,htgt,hbodyLocal,hs,hc,he,hl,targetRun,targetCode,sourceCode,sourceClock,?_,?_,continuations⟩
  · exact sourceCount
  · dsimp only [targetEntry,next,ns] at targetCount ⊢
    simp only [decClockCrepSemHOL] at targetCount ⊢
    omega

private theorem resultRel_terminal {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (out : Option (PanSemResultExact width)) (targetOut : Option (CrepResultHOLExact width))
    (rel : pcCompileCorrectResultRel ctxt s t out targetOut)
    (terminal : ∀ value, out ≠ some (.returned value)) :
    ∀ returned, targetOut ≠ some (.return returned) := by
  cases out with
  | none => simp [pcCompileCorrectResultRel] at rel; simp [rel.1]
  | some r =>
    cases r <;> simp_all [pcCompileCorrectResultRel]
    case exception id value =>
      split at rel <;> simp_all


open Flapjack.PanSemStateFiniteExact in
/-- Terminal declaration-call outcomes count the callee but no continuation. -/
theorem decCall_terminal_bridge {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (result : Option (PanSemResultExact width)) (sourcePost : PanSemStateFiniteExact width σ)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (result,sourcePost))
    (nonerror : result ≠ some .error) (terminal : ∀ value, result ≠ some (.returned value)) :
    ∃ shapes : List (MlS × ShapeHOL),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      let sourceEntry := callEntryStateHOLFinite source locals
      let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
      source.code.lookup fname = some (shapes,body,rsh) ∧
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) ∧
      localisedProgHOL body = true ∧
      panToCrepStateRelFiniteExact sourceEntry targetEntry ∧
      codeRelExactHOLW next sourceEntry.code targetEntry.code ∧
      panToCrepExcpRelFiniteExact next.eids sourceEntry.eshapes ∧
      panToCrepLocalsRelFiniteExact next sourceEntry.locals targetEntry.locals ∧
      controlSteps (.decCall name shape fname argexps continuation) source = 1 + controlSteps body sourceEntry ∧
      CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target =
        (decCallSlots ctxt shape).length + 2 + CrepSteps.steps (compileProgExactHOLW next body) targetEntry := by
  classical
  obtain ⟨shapes,hsrc,hbodyLocal,htgt,callCount,hs,hc,he,hl⟩ :=
    decCall_entries ctxt fname shape argexps source target args body locals rsh hargs found clock stateRel codeRel excpRel localsRel localised
  let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
  let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
  let entry := callEntryStateHOLFinite source locals
  let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
  have correct : pcCompileCorrectAt body entry := (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨targetResult,targetPost,targetRun,_,_,_,resultRel⟩ :=
    correct result sourcePost targetEntry next bodyRun nonerror hs hc he hl hbodyLocal
  have targetTerminal := resultRel_terminal next sourcePost targetPost result targetResult resultRel terminal
  obtain ⟨shapes2,hsrc2,_,_,_,htargs,htlookup,_,_,_,_⟩ :=
    pcCompileCorrectCallPrelude source target ctxt fname argexps args body locals rsh hargs found stateRel codeRel excpRel localsRel localised
  have shapesEq : shapes2 = shapes := by rw [hsrc] at hsrc2; exact (congrArg Prod.fst (Option.some.inj hsrc2)).symm
  subst shapes2
  have hdist := pcCompileCorrectCallRetSlotsDistinct ctxt argexps (sizeOfShapeHOL shape) localsRel.2.1
  have targetClock : target.clock ≠ 0 := by rw [← stateRel.2.2.2.2.2.1]; exact clock
  have callTerminal := initializedCall_terminal target fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst)
    (args.flatMap flattenHOL) (compileProgExactHOLW next body) (tlcHOL ns args)
    (decCallSlots ctxt shape) targetResult targetPost htargs htlookup targetClock (decCallSlots_nodup ctxt shape) hdist targetRun targetTerminal
  have sourceCount := controlSteps_decCall_terminal name fname shape argexps continuation source args body locals rsh result sourcePost hargs found clock bodyRun terminal
  have targetCount := decCall_compiled_steps ctxt name fname shape argexps continuation target
  dsimp only at targetCount callTerminal
  rw [callCount] at targetCount
  rcases callRun : evalCrepSemHOLProgExact _ (.call (some (decCallSlots ctxt shape,none)) fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst)) with ⟨callResult,callPost⟩
  rw [callRun] at targetCount callTerminal
  cases callResult with
  | none => simp at callTerminal
  | some r =>
    simp only at targetCount
    refine ⟨shapes,hsrc,htgt,hbodyLocal,hs,hc,he,hl,sourceCount,?_⟩
    dsimp only [targetEntry,next,ns] at targetCount ⊢
    simp only [decClockCrepSemHOL] at targetCount ⊢
    omega

/-- At zero clock, a Crep call visits only itself and cannot continue. -/
theorem crep_call_zero {width : Nat} [NeZero width] {σ : Type}
    (ret : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
    (fname : MlS) (args : List (CrepExpHOL width)) (target : CrepSemHOLState width σ)
    (clock : target.clock = 0) : CrepSteps.steps (.call ret fname args) target = 1 ∧
       (evalCrepSemHOLProgExact target (.call ret fname args)).1 ≠ none := by
  constructor
  · rw [CrepSteps.steps.eq_def]
    cases hargs : args.mapM (evalCrepSemHOLExp target) with
    | none => simp [hargs]
    | some vals =>
      cases hfind : target.code.lookup fname with
      | none => simp [hargs,hfind]
      | some entry => obtain ⟨params,body⟩ := entry; simp [hargs,hfind,clock]
  · rw [evalCrepSemHOLProgExact_call_holShape]
    cases hargs : args.mapM (evalCrepSemHOLExp target) with
    | none => simp
    | some vals =>
      cases hfind : lookupCodeFiniteHOL target.code fname vals vals.length with
      | none => simp [hfind]
      | some entry =>
        obtain ⟨body,locals⟩ := entry
        simp only [hfind,clock,if_true]; split <;> simp

open Flapjack.PanSemStateFiniteExact in
/-- A non-error tail call has evaluated arguments and a matching code entry. -/
theorem tailCall_nonerror_reaches {width : Nat} [NeZero width] {σ : Type}
    (fname : MlS) (argexps : List (ExpHOL width))
    (source post : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.call none fname argexps) = (result,post))
    (nonerror : result ≠ some .error) :
    ∃ args body locals rsh,
      source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args ∧
      lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh) := by
  cases hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
    have h := evaluateHOLFiniteState_call_args_none source none fname argexps hargs
    rw [h] at run
    exact False.elim (nonerror (Prod.mk.inj run).1.symm)
  | some args =>
    cases hfound : lookupCodeHOLFinite source.code.lookup fname args with
    | none =>
      have h := evaluateHOLFiniteState_call_lookup_none source none fname argexps args hargs hfound
      rw [h] at run
      exact False.elim (nonerror (Prod.mk.inj run).1.symm)
    | some entry =>
      obtain ⟨body,locals,rsh⟩ := entry
      exact ⟨args,body,locals,rsh,rfl,hfound⟩

/-- The quantitative induction step for a reached tail call. -/
theorem tailCall_codeBound_from_body {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (fname : MlS) (argexps : List (ExpHOL width))
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (programs : List (MlS × List Nat × CrepProgHOL width)) (K : Nat)
    (tableWeight : CrepSteps.codeWeight programs ≤ K)
    (code : target.code = alistToFmapCodeExact programs)
    (run : source.evaluateHOLFiniteState (.call none fname argexps) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (bodyIH : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL),
      source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args →
      PanSemStateFiniteExact.lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh) →
      ∀ (shapes : List (MlS × ShapeHOL)),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      source.code.lookup fname = some (shapes,body,rsh) →
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) →
      (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).clock < source.clock →
      localisedProgHOL body = true →
      panToCrepStateRelFiniteExact (PanSemStateFiniteExact.callEntryStateHOLFinite source locals)
        {decClockCrepSemHOL target with locals := tlcHOL ns args} →
      codeRelExactHOLW next (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).code
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).code →
      panToCrepExcpRelFiniteExact next.eids (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).eshapes →
      panToCrepLocalsRelFiniteExact next (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).locals
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).locals →
      ∀ (calleeResult : Option (PanSemResultExact width)) (calleePost : PanSemStateFiniteExact width σ),
      (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (calleeResult,calleePost) →
      calleeResult ≠ some .error →
      CrepSteps.steps (compileProgExactHOLW next body) {decClockCrepSemHOL target with locals := tlcHOL ns args} ≤
        K * controlSteps body (PanSemStateFiniteExact.callEntryStateHOLFinite source locals)) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.call none fname argexps)) target ≤
      K * controlSteps (.call none fname argexps) source := by
  by_cases clock : source.clock = 0
  · have targetClock : target.clock = 0 := stateRel.2.2.2.2.2.1.symm.trans clock
    have count := (crep_call_zero none fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst) target targetClock).1
    have sourcePositive := controlSteps_pos (.call none fname argexps) source
    have weightPositive : ∀ ps : List (MlS × List Nat × CrepProgHOL width), 1 ≤ CrepSteps.codeWeight ps := by
      intro ps
      induction ps with
      | nil => simp [CrepSteps.codeWeight]
      | cons row rest ih =>
        change 1 ≤ max (CrepSteps.statementWeight row.2.2) (CrepSteps.codeWeight rest)
        exact Nat.le_trans ih (Nat.le_max_right _ _)
    have weightPositive : 1 ≤ K := (weightPositive programs).trans tableWeight
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW] at ⊢
    rw [count]
    nlinarith
  · obtain ⟨args,body,locals,rsh,hargs,found⟩ := tailCall_nonerror_reaches fname argexps source sourceFinal result run nonerror
    obtain ⟨shapes,hsrc,hlocal,htgt,hsource,htarget,hs,hc,he,hl⟩ :=
      tailCall_entries ctxt fname argexps source target args body locals rsh hargs found clock stateRel codeRel excpRel localsRel localised
    have smaller : (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).clock < source.clock := by
      simp only [PanSemStateFiniteExact.callEntryStateHOLFinite]
      omega
    rcases bodyRun : (PanSemStateFiniteExact.callEntryStateHOLFinite source locals).evaluateHOLFiniteState body with ⟨calleeResult,calleePost⟩
    have bodyNonerror : calleeResult ≠ some .error := by
      intro bad
      subst calleeResult
      have failed := evaluateHOLFiniteState_call_body_fallback source none fname argexps args body locals rsh
        .error calleePost hargs found clock bodyRun (Or.inl rfl)
      rw [failed] at run
      exact nonerror (Prod.mk.inj run).1.symm
    have b := bodyIH args body locals rsh hargs found shapes hsrc htgt smaller hlocal hs hc he hl calleeResult calleePost bodyRun bodyNonerror
    rw [hsource,htarget]
    have positive : 1 ≤ K := by
      have w := SteppedFlapjack.CrepToLoopSteps.lookup_statementWeight_le_codeWeight programs fname
        (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))
        (compileProgExactHOLW (ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd)
          (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))) body) (by simpa [code] using htgt)
      have p := CrepSteps.statementWeight_pos (compileProgExactHOLW (ctxtFcExactHOL ctxt.funcs ctxt.eids
        (shapes.map Prod.fst) (shapes.map Prod.snd) (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))) body)
      omega
    nlinarith

/-- A zero-clock declaration call stays within its generated slot overhead. -/
theorem decCall_zero_bound {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (args : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ) (K : Nat)
    (clock : source.clock = 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (weight : CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname args continuation)) ≤ K) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname args continuation)) target ≤
      K * controlSteps (.decCall name shape fname args continuation) source := by
  let names := decCallSlots ctxt shape
  let pre : CrepSemHOLState width σ := {target with locals := target.locals.updateListEq (names.zip (List.replicate names.length (.word 0)))}
  let call : CrepProgHOL width := .call (some (names,none)) fname ((compileExpExactHOLWList ctxt args).flatMap Prod.fst)
  have preClock : pre.clock = 0 := stateRel.2.2.2.2.2.1.symm.trans clock
  have zero := crep_call_zero (some (names,none)) fname ((compileExpExactHOLWList ctxt args).flatMap Prod.fst) pre preClock
  have count := decCall_compiled_steps ctxt name fname shape args continuation target
  change CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname args continuation)) target =
    names.length + (1 + CrepSteps.steps call pre + match evalCrepSemHOLProgExact pre call with
      | (none,post) => CrepSteps.steps (compileProgExactHOLW (decCallCtxt ctxt name shape) continuation) post
      | _ => 0) at count
  rcases run : evalCrepSemHOLProgExact pre call with ⟨out,post⟩
  rw [run] at count
  have noNone : out ≠ none := by simpa [call,run] using zero.2
  cases out with
  | none => exact False.elim (noNone rfl)
  | some r =>
    simp only at count
    have one : CrepSteps.steps call pre = 1 := zero.1
    rw [one] at count
    have overhead : names.length + 2 ≤ K := by
      rw [decCall_statementWeight] at weight
      simp [names,decCallSlots]
      omega
    have positive := controlSteps_pos (.decCall name shape fname args continuation) source
    rw [count]
    nlinarith

open Flapjack.PanSemStateFiniteExact

/-- Returning-call induction combines the reached callee and continuation. -/
theorem decCall_return_bound_from_induction {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (value : ValueHOL width) (sourcePost sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (K : Nat)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (run : source.evaluateHOLFiniteState (.decCall name shape fname argexps continuation) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (some (.returned value),sourcePost))
    (valid : shapeOfHOLExact value = shape) (returnValid : shapeOfHOLExact value = rsh)
    (weight : CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) ≤ K)
    (bodyIH : ∀ (shapes : List (MlS × ShapeHOL)),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      source.code.lookup fname = some (shapes,body,rsh) →
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) →
      (callEntryStateHOLFinite source locals).clock < source.clock →
      localisedProgHOL body = true →
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite source locals)
        {decClockCrepSemHOL target with locals := tlcHOL ns args} →
      codeRelExactHOLW next (callEntryStateHOLFinite source locals).code
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).code →
      panToCrepExcpRelFiniteExact next.eids (callEntryStateHOLFinite source locals).eshapes →
      panToCrepLocalsRelFiniteExact next (callEntryStateHOLFinite source locals).locals
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).locals →
      ∀ (calleeResult : Option (PanSemResultExact width)) (calleePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (calleeResult,calleePost) →
      calleeResult ≠ some .error →
      CrepSteps.steps (compileProgExactHOLW next body) {decClockCrepSemHOL target with locals := tlcHOL ns args} ≤
        K * controlSteps body (callEntryStateHOLFinite source locals))
    (contIH : ∀ targetPost : CrepSemHOLState width σ,
      let sourceCont := setVarHOLFinite name value {sourcePost with locals := source.locals}
      let targetCont := {targetPost with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL value))}
      targetPost.code = target.code →
      sourcePost.code = source.code →
      sourcePost.clock < source.clock →
      ∀ continuationPost : PanSemStateFiniteExact width σ,
      sourceCont.evaluateHOLFiniteState continuation = (result,continuationPost) →
      result ≠ some .error →
      panToCrepStateRelFiniteExact sourceCont targetCont →
      codeRelExactHOLW (decCallCtxt ctxt name shape) sourceCont.code targetCont.code →
      panToCrepExcpRelFiniteExact (decCallCtxt ctxt name shape).eids sourceCont.eshapes →
      panToCrepLocalsRelFiniteExact (decCallCtxt ctxt name shape) sourceCont.locals targetCont.locals →
      CrepSteps.steps (compileProgExactHOLW (decCallCtxt ctxt name shape) continuation) targetCont ≤
        K * controlSteps continuation sourceCont) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target ≤
      K * controlSteps (.decCall name shape fname argexps continuation) source := by
  obtain ⟨shapes,targetPost,hsrc,htgt,hlocal,bs,bc,be,bl,_,hcode,hsourceCode,hpostClock,hsource,htarget,hs,hc,he,hl⟩ :=
    decCall_return_bridge ctxt name fname shape argexps continuation source target args body locals rsh value sourcePost
      hargs found clock stateRel codeRel excpRel localsRel localised bodyRun valid returnValid
  have smaller : (callEntryStateHOLFinite source locals).clock < source.clock := by
    simp only [callEntryStateHOLFinite]
    omega
  have b := bodyIH shapes hsrc htgt smaller hlocal bs bc be bl (some (.returned value)) sourcePost bodyRun (by simp)
  rcases contRun : (setVarHOLFinite name value {sourcePost with locals := source.locals}).evaluateHOLFiniteState continuation with ⟨contResult,contPost⟩
  have resultEq : contResult = result := by
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [hargs,found,clock,if_false,bodyRun] at run
    have hv : shapeEqHOL (shapeOfHOLExact value) shape = true := (shapeEqHOL_eq_true _ _).mpr valid
    have hr : shapeEqHOL (shapeOfHOLExact value) rsh = true := (shapeEqHOL_eq_true _ _).mpr returnValid
    simp only [hv,hr,Bool.true_and,if_true,contRun] at run
    exact (Prod.mk.inj run).1
  subst contResult
  have c := contIH targetPost hcode hsourceCode hpostClock contPost contRun nonerror hs hc he hl
  have overhead : (decCallSlots ctxt shape).length + 2 ≤ K := by
    rw [decCall_statementWeight] at weight
    simp [decCallSlots]
    omega
  rw [hsource,htarget]
  nlinarith

/-- Terminal calls do not visit the continuation. -/
theorem decCall_terminal_bound_from_induction {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (result : Option (PanSemResultExact width)) (sourcePost : PanSemStateFiniteExact width σ) (K : Nat)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (result,sourcePost))
    (nonerror : result ≠ some .error) (terminal : ∀ value, result ≠ some (.returned value))
    (weight : CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) ≤ K)
    (bodyIH : ∀ (shapes : List (MlS × ShapeHOL)),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      source.code.lookup fname = some (shapes,body,rsh) →
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) →
      (callEntryStateHOLFinite source locals).clock < source.clock →
      localisedProgHOL body = true →
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite source locals)
        {decClockCrepSemHOL target with locals := tlcHOL ns args} →
      codeRelExactHOLW next (callEntryStateHOLFinite source locals).code
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).code →
      panToCrepExcpRelFiniteExact next.eids (callEntryStateHOLFinite source locals).eshapes →
      panToCrepLocalsRelFiniteExact next (callEntryStateHOLFinite source locals).locals
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).locals →
      ∀ (calleeResult : Option (PanSemResultExact width)) (calleePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (calleeResult,calleePost) →
      calleeResult ≠ some .error →
      CrepSteps.steps (compileProgExactHOLW next body) {decClockCrepSemHOL target with locals := tlcHOL ns args} ≤
        K * controlSteps body (callEntryStateHOLFinite source locals))
 :
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target ≤
      K * controlSteps (.decCall name shape fname argexps continuation) source := by
  obtain ⟨shapes,hsrc,htgt,hlocal,bs,bc,be,bl,hsource,htarget⟩ :=
    decCall_terminal_bridge ctxt name fname shape argexps continuation source target args body locals rsh result sourcePost
      hargs found clock stateRel codeRel excpRel localsRel localised bodyRun nonerror terminal
  have smaller : (callEntryStateHOLFinite source locals).clock < source.clock := by
    simp only [callEntryStateHOLFinite]
    omega
  have b := bodyIH shapes hsrc htgt smaller hlocal bs bc be bl result sourcePost bodyRun nonerror
  have overhead : (decCallSlots ctxt shape).length + 2 ≤ K := by
    rw [decCall_statementWeight] at weight
    simp [decCallSlots]
    omega
  rw [hsource,htarget]
  nlinarith

/-- All entered declaration-call outcomes share the same induction step. -/
theorem decCall_entered_bound_from_induction {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (args : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL)
    (sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (K : Nat)
    (hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args)
    (found : lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh))
    (clock : source.clock ≠ 0) (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (run : source.evaluateHOLFiniteState (.decCall name shape fname argexps continuation) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (weight : CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) ≤ K)
    (bodyIH : ∀ (shapes : List (MlS × ShapeHOL)),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      source.code.lookup fname = some (shapes,body,rsh) →
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) →
      (callEntryStateHOLFinite source locals).clock < source.clock →
      localisedProgHOL body = true →
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite source locals)
        {decClockCrepSemHOL target with locals := tlcHOL ns args} →
      codeRelExactHOLW next (callEntryStateHOLFinite source locals).code
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).code →
      panToCrepExcpRelFiniteExact next.eids (callEntryStateHOLFinite source locals).eshapes →
      panToCrepLocalsRelFiniteExact next (callEntryStateHOLFinite source locals).locals
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).locals →
      ∀ (calleeResult : Option (PanSemResultExact width)) (calleePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (calleeResult,calleePost) →
      calleeResult ≠ some .error →
      CrepSteps.steps (compileProgExactHOLW next body) {decClockCrepSemHOL target with locals := tlcHOL ns args} ≤
        K * controlSteps body (callEntryStateHOLFinite source locals))
    (contIH : ∀ (value : ValueHOL width) (sourcePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (some (.returned value),sourcePost) →
      ∀ targetPost : CrepSemHOLState width σ,
      let sourceCont := setVarHOLFinite name value {sourcePost with locals := source.locals}
      let targetCont := {targetPost with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL value))}
      targetPost.code = target.code →
      sourcePost.code = source.code →
      sourcePost.clock < source.clock →
      ∀ continuationPost : PanSemStateFiniteExact width σ,
      sourceCont.evaluateHOLFiniteState continuation = (result,continuationPost) →
      result ≠ some .error →
      panToCrepStateRelFiniteExact sourceCont targetCont →
      codeRelExactHOLW (decCallCtxt ctxt name shape) sourceCont.code targetCont.code →
      panToCrepExcpRelFiniteExact (decCallCtxt ctxt name shape).eids sourceCont.eshapes →
      panToCrepLocalsRelFiniteExact (decCallCtxt ctxt name shape) sourceCont.locals targetCont.locals →
      CrepSteps.steps (compileProgExactHOLW (decCallCtxt ctxt name shape) continuation) targetCont ≤
        K * controlSteps continuation sourceCont) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target ≤
      K * controlSteps (.decCall name shape fname argexps continuation) source := by
  rcases bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body with ⟨out,post⟩
  have bodyNonerror : out ≠ some .error := by
    intro bad
    subst out
    have hr := run
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
    simp only [hargs,found,clock,if_false,bodyRun] at hr
    exact nonerror (Prod.mk.inj hr).1.symm
  have hr := run
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr
  simp only [hargs,found,clock,if_false,bodyRun] at hr
  cases out with
  | none => simp at hr; exact False.elim (nonerror hr.1.symm)
  | some r =>
    cases r with
    | returned value =>
      by_cases hv : shapeEqHOL (shapeOfHOLExact value) shape = true
      · by_cases hret : shapeEqHOL (shapeOfHOLExact value) rsh = true
        · exact decCall_return_bound_from_induction ctxt name fname shape argexps continuation source target args body locals rsh
            value post sourceFinal result K hargs found clock stateRel codeRel excpRel localsRel localised run nonerror bodyRun
            ((shapeEqHOL_eq_true _ _).mp hv) ((shapeEqHOL_eq_true _ _).mp hret) weight bodyIH (contIH value post bodyRun)
        · simp [hv,hret] at hr; exact False.elim (nonerror hr.1.symm)
      · simp [hv] at hr; exact False.elim (nonerror hr.1.symm)
    | «break» => simp at hr; exact False.elim (nonerror hr.1.symm)
    | «continue» => simp at hr; exact False.elim (nonerror hr.1.symm)
    | error => exact False.elim (bodyNonerror rfl)
    | timeOut =>
      exact decCall_terminal_bound_from_induction ctxt name fname shape argexps continuation source target args body locals rsh
          (some .timeOut) post K hargs found clock stateRel codeRel excpRel localsRel localised bodyRun (by simp) (by simp) weight bodyIH
    | finalFfi event =>
      exact decCall_terminal_bound_from_induction ctxt name fname shape argexps continuation source target args body locals rsh
          (some (.finalFfi event)) post K hargs found clock stateRel codeRel excpRel localsRel localised bodyRun (by simp) (by simp) weight bodyIH
    | exception eid value =>
      exact decCall_terminal_bound_from_induction ctxt name fname shape argexps continuation source target args body locals rsh
          (some (.exception eid value)) post K hargs found clock stateRel codeRel excpRel localsRel localised bodyRun (by simp) (by simp) weight bodyIH

/-- A non-error declaration call supplies arguments and a code entry. -/
theorem decCall_nonerror_reaches {width : Nat} [NeZero width] {σ : Type}
    (name fname : MlS) (shape : ShapeHOL) (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source post : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (run : source.evaluateHOLFiniteState (.decCall name shape fname argexps continuation) = (result,post))
    (nonerror : result ≠ some .error) :
    ∃ args body locals rsh,
      source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args ∧
      lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh) := by
  cases hargs : source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps with
  | none =>
    have h := evaluateHOLFiniteState_decCall_args_none source name shape fname argexps continuation hargs
    rw [h] at run
    exact False.elim (nonerror (Prod.mk.inj run).1.symm)
  | some args =>
    cases hfound : lookupCodeHOLFinite source.code.lookup fname args with
    | none =>
      have h := evaluateHOLFiniteState_decCall_lookup_none source name shape fname argexps continuation args hargs hfound
      rw [h] at run
      exact False.elim (nonerror (Prod.mk.inj run).1.symm)
    | some entry =>
      obtain ⟨body,locals,rsh⟩ := entry
      exact ⟨args,body,locals,rsh,rfl,hfound⟩

/-- The declaration-call induction uses the source run to select its callee and outcome. -/
theorem decCall_bound_from_induction {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (name fname : MlS) (shape : ShapeHOL)
    (argexps : List (ExpHOL width)) (continuation : ProgHOL width)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width σ)
    (sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (K : Nat)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals)
    (localised : everyExpListHOL localisedExpHOL argexps = true)
    (run : source.evaluateHOLFiniteState (.decCall name shape fname argexps continuation) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (weight : CrepSteps.statementWeight (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) ≤ K)
    (bodyIH : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL),
      source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args →
      lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh) →
      ∀ (shapes : List (MlS × ShapeHOL)),
      let ns := List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd)))
      let next := ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd) ns
      source.code.lookup fname = some (shapes,body,rsh) →
      target.code.lookup fname = some (ns,compileProgExactHOLW next body) →
      (callEntryStateHOLFinite source locals).clock < source.clock →
      localisedProgHOL body = true →
      panToCrepStateRelFiniteExact (callEntryStateHOLFinite source locals)
        {decClockCrepSemHOL target with locals := tlcHOL ns args} →
      codeRelExactHOLW next (callEntryStateHOLFinite source locals).code
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).code →
      panToCrepExcpRelFiniteExact next.eids (callEntryStateHOLFinite source locals).eshapes →
      panToCrepLocalsRelFiniteExact next (callEntryStateHOLFinite source locals).locals
        ({decClockCrepSemHOL target with locals := tlcHOL ns args}).locals →
      ∀ (calleeResult : Option (PanSemResultExact width)) (calleePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (calleeResult,calleePost) →
      calleeResult ≠ some .error →
      CrepSteps.steps (compileProgExactHOLW next body) {decClockCrepSemHOL target with locals := tlcHOL ns args} ≤
        K * controlSteps body (callEntryStateHOLFinite source locals))
    (contIH : ∀ (args : List (ValueHOL width)) (body : ProgHOL width)
      (locals : HolFiniteMapExact MlS (ValueHOL width)) (rsh : ShapeHOL),
      source.evalListHOLFinite (h := fun address => Classical.propDecidable (source.memaddrs address)) argexps = some args →
      lookupCodeHOLFinite source.code.lookup fname args = some (body,locals,rsh) →
      ∀ (value : ValueHOL width) (sourcePost : PanSemStateFiniteExact width σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState body = (some (.returned value),sourcePost) →
      ∀ targetPost : CrepSemHOLState width σ,
      let sourceCont := setVarHOLFinite name value {sourcePost with locals := source.locals}
      let targetCont := {targetPost with locals := target.locals.updateListEq ((decCallSlots ctxt shape).zip (flattenHOL value))}
      targetPost.code = target.code →
      sourcePost.code = source.code →
      sourcePost.clock < source.clock →
      ∀ continuationPost : PanSemStateFiniteExact width σ,
      sourceCont.evaluateHOLFiniteState continuation = (result,continuationPost) →
      result ≠ some .error →
      panToCrepStateRelFiniteExact sourceCont targetCont →
      codeRelExactHOLW (decCallCtxt ctxt name shape) sourceCont.code targetCont.code →
      panToCrepExcpRelFiniteExact (decCallCtxt ctxt name shape).eids sourceCont.eshapes →
      panToCrepLocalsRelFiniteExact (decCallCtxt ctxt name shape) sourceCont.locals targetCont.locals →
      CrepSteps.steps (compileProgExactHOLW (decCallCtxt ctxt name shape) continuation) targetCont ≤
        K * controlSteps continuation sourceCont) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.decCall name shape fname argexps continuation)) target ≤
      K * controlSteps (.decCall name shape fname argexps continuation) source := by
  by_cases clock : source.clock = 0
  · exact decCall_zero_bound ctxt name fname shape argexps continuation source target K clock stateRel weight
  · obtain ⟨args,body,locals,rsh,hargs,found⟩ := decCall_nonerror_reaches name fname shape argexps continuation source sourceFinal result run nonerror
    exact decCall_entered_bound_from_induction ctxt name fname shape argexps continuation source target args body locals rsh
      sourceFinal result K hargs found clock stateRel codeRel excpRel localsRel localised run nonerror weight
      (bodyIH args body locals rsh hargs found) (contIH args body locals rsh hargs found)

/-- Frontend syntax closed under direct tail calls and declaration calls. -/
inductive CallFrontend {width : Nat} [NeZero width] : PanToCrepContextExact width → ProgHOL width → Prop
  | base {ctxt p} : FrontendProgram ctxt p → CallFrontend ctxt p
  | tail {ctxt fname args} : (∀ e ∈ args, FrontendScalar ctxt e) → CallFrontend ctxt (.call none fname args)
  | decCall {ctxt name shape fname args cont} : (∀ e ∈ args, FrontendScalar ctxt e) →
      CallFrontend (decCallCtxt ctxt name shape) cont → CallFrontend ctxt (.decCall name shape fname args cont)
  | decl {ctxt name e body} : FrontendScalar ctxt e → CallFrontend (scalarDeclContext ctxt name) body →
      CallFrontend ctxt (.dec name .one e body)
  | seq {ctxt a b} : CallFrontend ctxt a → CallFrontend ctxt b → CallFrontend ctxt (.seq a b)
  | ite {ctxt e a b} : FrontendScalar ctxt e → CallFrontend ctxt a → CallFrontend ctxt b → CallFrontend ctxt (.ite e a b)
  | while {ctxt e body} : FrontendScalar ctxt e → CallFrontend ctxt body → CallFrontend ctxt (.while e body)

theorem callFrontend_localised {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    {p : ProgHOL width} (h : CallFrontend ctxt p) : localisedProgHOL p = true := by
  induction h with
  | base h => exact frontendProgram_localised h
  | @tail ctxt fname args ha => simpa [localisedProgHOL] using frontendArguments_localised ctxt args ha
  | @decCall ctxt name shape fname args cont ha hb ih =>
    simp [localisedProgHOL,frontendArguments_localised ctxt args ha,ih]
  | decl he hb ih => simp [localisedProgHOL,frontendScalar_localised he,ih]
  | seq ha hb iha ihb => simp [localisedProgHOL,iha,ihb]
  | ite he ha hb iha ihb => simp [localisedProgHOL,frontendScalar_localised he,iha,ihb]
  | «while» he hb ih => simp [localisedProgHOL,frontendScalar_localised he,ih]

/-- All source functions satisfy the call-aware syntax in their actual callee contexts. -/
def CallFrontendCode {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) : Prop :=
  ∀ name params body rsh, code.lookup name = some (params,body,rsh) →
    let ns := List.range (sizeOfShapeHOL (.comb (params.map Prod.snd)))
    CallFrontend (ctxtFcExactHOL ctxt.funcs ctxt.eids (params.map Prod.fst) (params.map Prod.snd) ns) body

/-- Function-table support depends only on the function and exception maps. -/
theorem callFrontendCode_context {width : Nat} [NeZero width]
    (a b : PanToCrepContextExact width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (funcs : a.funcs = b.funcs) (eids : a.eids = b.eids) (h : CallFrontendCode a code) :
    CallFrontendCode b code := by
  intro name params body rsh found
  simpa only [← funcs,← eids] using h name params body rsh found

theorem callFrontendCode_callee {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (vs : List MlS) (shapes : List ShapeHOL) (ns : List Nat) (h : CallFrontendCode ctxt code) :
    CallFrontendCode (ctxtFcExactHOL ctxt.funcs ctxt.eids vs shapes ns) code := by
  apply callFrontendCode_context ctxt _ code <;> simp [ctxtFcExactHOL,h]

theorem callFrontendCode_decl {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (h : CallFrontendCode ctxt code) :
    CallFrontendCode (scalarDeclContext ctxt name) code := by
  apply callFrontendCode_context ctxt _ code <;> simp [scalarDeclContext,h]

theorem callFrontendCode_decCall {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
    (name : MlS) (shape : ShapeHOL) (h : CallFrontendCode ctxt code) :
    CallFrontendCode (decCallCtxt ctxt name shape) code := by
  apply callFrontendCode_context ctxt _ code <;> simp [h]

set_option maxHeartbeats 3000000 in
private theorem callFrontend_global {width : Nat} [NeZero width] (limit : Nat) :
    ∀ (ctxt : PanToCrepContextExact width) (p : ProgHOL width)
      (sourceTable : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (programs : List (MlS × List Nat × CrepProgHOL width)) (K : Nat),
      CallFrontend ctxt p → CallFrontendCode ctxt sourceTable → CrepSteps.codeWeight programs ≤ K →
      ProgramBound ctxt p limit sourceTable (alistToFmapCodeExact programs) K := by
  induction limit using Nat.strong_induction_on with
  | h limit ih =>
    intro ctxt p sourceTable programs K shape supported weight
    induction shape with
    | base h => exact frontendProgramBound h limit sourceTable (alistToFmapCodeExact programs) K
    | @tail ctxt fname argexps ha =>
      intro programWeight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
      apply tailCall_codeBound_from_body ctxt fname argexps source target sourceFinal result programs K weight targetTable run nonerror stateRel codeRel excpRel localsRel
        (frontendArguments_localised ctxt argexps ha)
      intro args body locals rsh hargs found shapes ns next hsrc htgt smaller hlocal hs hc he hl calleeResult calleePost bodyRun bodyNonerror
      let entry := PanSemStateFiniteExact.callEntryStateHOLFinite source locals
      let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
      have lookup : sourceTable.lookup fname = some (shapes,body,rsh) := by simpa [← sourceTableEq] using hsrc
      have bodyShape : CallFrontend next body := supported fname shapes body rsh lookup
      have bodySupport : CallFrontendCode next sourceTable := callFrontendCode_callee ctxt sourceTable _ _ _ supported
      have bodyWeight : CrepSteps.statementWeight (compileProgExactHOLW next body) ≤ K := by
        have h := CrepToLoopSteps.lookup_statementWeight_le_codeWeight programs fname ns (compileProgExactHOLW next body) (by simpa [← targetTable] using htgt)
        exact h.trans weight
      have lower : entry.clock < limit := by simp only [entry] at *; omega
      have bound := ih entry.clock lower next body sourceTable programs K bodyShape bodySupport weight
      exact bound bodyWeight entry calleePost calleeResult targetEntry
        (by simpa [targetEntry,decClockCrepSemHOL] using targetTable)
        (by simpa [entry,PanSemStateFiniteExact.callEntryStateHOLFinite] using sourceTableEq)
        (Nat.le_refl _) bodyRun bodyNonerror hs hc he hl
    | @decCall ctxt name shape fname argexps cont ha hb ihb =>
      intro programWeight σ source sourceFinal result target targetTable sourceTableEq sourceLimit run nonerror stateRel codeRel excpRel localsRel
      apply decCall_bound_from_induction ctxt name fname shape argexps cont source target sourceFinal result K stateRel codeRel excpRel localsRel
        (frontendArguments_localised ctxt argexps ha) run nonerror programWeight
      · intro args body locals rsh hargs found shapes ns next hsrc htgt smaller hlocal hs hc he hl calleeResult calleePost bodyRun bodyNonerror
        let entry := PanSemStateFiniteExact.callEntryStateHOLFinite source locals
        let targetEntry := {decClockCrepSemHOL target with locals := tlcHOL ns args}
        have lookup : sourceTable.lookup fname = some (shapes,body,rsh) := by simpa [← sourceTableEq] using hsrc
        have bodyShape : CallFrontend next body := supported fname shapes body rsh lookup
        have bodySupport : CallFrontendCode next sourceTable := callFrontendCode_callee ctxt sourceTable _ _ _ supported
        have bodyWeight : CrepSteps.statementWeight (compileProgExactHOLW next body) ≤ K := by
          have h := CrepToLoopSteps.lookup_statementWeight_le_codeWeight programs fname ns (compileProgExactHOLW next body) (by simpa [← targetTable] using htgt)
          exact h.trans weight
        have lower : entry.clock < limit := by simp only [entry] at *; omega
        have bound := ih entry.clock lower next body sourceTable programs K bodyShape bodySupport weight
        exact bound bodyWeight entry calleePost calleeResult targetEntry
          (by simpa [targetEntry,decClockCrepSemHOL] using targetTable)
          (by simpa [entry,PanSemStateFiniteExact.callEntryStateHOLFinite] using sourceTableEq)
          (Nat.le_refl _) bodyRun bodyNonerror hs hc he hl
      · intro args body locals rsh hargs found value sourcePost bodyRun targetPost sourceCont targetCont targetCode sourceCode smaller continuationPost contRun contNonerror contState contCode contExcp contLocals
        have contWeight : CrepSteps.statementWeight (compileProgExactHOLW (decCallCtxt ctxt name shape) cont) ≤ K := by
          rw [decCall_statementWeight] at programWeight
          omega
        have bound := ihb (callFrontendCode_decCall ctxt sourceTable name shape supported)
        apply bound contWeight sourceCont continuationPost result targetCont
        · simpa [targetCont,targetCode] using targetTable
        · simpa [sourceCont,PanSemStateFiniteExact.setVarHOLFinite,sourceCode] using sourceTableEq
        · simp only [sourceCont,PanSemStateFiniteExact.setVarHOLFinite]
          omega
        · exact contRun
        · exact contNonerror
        · exact contState
        · exact contCode
        · exact contExcp
        · exact contLocals
    | decl he hb ihb =>
      apply programBound_decl _ _ _ _ limit sourceTable (alistToFmapCodeExact programs) K he
      exact ihb (callFrontendCode_decl _ _ _ supported)
    | seq ha hb iha ihb =>
      exact programBound_seq _ _ _ limit sourceTable (alistToFmapCodeExact programs) K (callFrontend_localised ha) (iha supported) (ihb supported)
    | ite he ha hb iha ihb =>
      exact programBound_ite _ _ _ _ limit sourceTable (alistToFmapCodeExact programs) K he (iha supported) (ihb supported)
    | «while» he hb ihb =>
      exact programBound_while _ _ _ limit sourceTable (alistToFmapCodeExact programs) K he (callFrontend_localised hb) (ihb supported)

/-- The actual source execution has a Crep visit bound computed from the
compiled entry and the actual function table, including nested calls. -/
theorem callFrontend_compiled_steps {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width) (program : ProgHOL width)
    (shape : CallFrontend ctxt program)
    (source sourceFinal : PanSemStateFiniteExact width σ) (result : Option (PanSemResultExact width))
    (target : CrepSemHOLState width σ) (programs : List (MlS × List Nat × CrepProgHOL width))
    (table : target.code = alistToFmapCodeExact programs) (supported : CallFrontendCode ctxt source.code)
    (run : source.evaluateHOLFiniteState program = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (stateRel : panToCrepStateRelFiniteExact source target) (codeRel : codeRelExactHOLW ctxt source.code target.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids source.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals) :
    CrepSteps.steps (compileProgExactHOLW ctxt program) target ≤
      max (CrepSteps.statementWeight (compileProgExactHOLW ctxt program)) (CrepSteps.codeWeight programs) * controlSteps program source := by
  let K := max (CrepSteps.statementWeight (compileProgExactHOLW ctxt program)) (CrepSteps.codeWeight programs)
  have bound := callFrontend_global source.clock ctxt program source.code programs K shape supported (Nat.le_max_right _ _)
  exact bound (Nat.le_max_left _ _) source sourceFinal result target table rfl (Nat.le_refl _) run nonerror stateRel codeRel excpRel localsRel

end SteppedFlapjack.PanToCrepSteps
