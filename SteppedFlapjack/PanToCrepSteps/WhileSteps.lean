import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.PanToCrepSteps.FrontendProgram
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel

/-! Quantitative correctness of Pancake while compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- For a non-error source run, the actual compiled Crep while visits at most
the body factor per Pancake control visit when that factor is positive. -/
private theorem while_compiled_steps_compositional {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : FrontendScalar context condition)
    (bodyFactor : Nat) (factorPositive : 1 ≤ bodyFactor)
    (bodyBound : ∀ (bs bf : PanSemStateFiniteExact width σ) (br : Option (PanSemResultExact width))
      (bt : CrepSemHOLState width σ),
      bs.evaluateHOLFiniteState body = (br,bf) → br ≠ some .error →
      panToCrepStateRelFiniteExact bs bt → codeRelExactHOLW context bs.code bt.code →
      panToCrepExcpRelFiniteExact context.eids bs.eshapes →
      panToCrepLocalsRelFiniteExact context bs.locals bt.locals → localisedProgHOL body = true →
      CrepSteps.steps (compileProgExactHOLW context body) bt ≤ bodyFactor * controlSteps body bs)
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
          bodyRun bodyNonerror bodyState codeRel excpRel localsRel locs.2
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
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result targetPost tailRun nonerror
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


/-- Internal induction predicate: all related executions are bounded by the
size of the actual Crep output times the source control visits. -/
private def ProgramBound {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (program : ProgHOL width) : Prop :=
  ∀ {σ : Type} (source sourceFinal : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width)) (target : CrepSemHOLState width σ),
    source.evaluateHOLFiniteState program = (result,sourceFinal) → result ≠ some .error →
    panToCrepStateRelFiniteExact source target → codeRelExactHOLW context source.code target.code →
    panToCrepExcpRelFiniteExact context.eids source.eshapes →
    panToCrepLocalsRelFiniteExact context source.locals target.locals →
    CrepSteps.steps (compileProgExactHOLW context program) target ≤
      CrepSteps.statementWeight (compileProgExactHOLW context program) * controlSteps program source

/-- Sequence composition for the structural induction. -/
private theorem programBound_seq {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (a b : ProgHOL width)
    (aShape : FrontendProgram context a) (aBound : ProgramBound context a)
    (bBound : ProgramBound context b) : ProgramBound context (.seq a b) := by
  intro σ source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
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
      (frontendProgram_localised aShape)
  have firstBound := aBound source middle firstResult target firstRun firstNonerror stateRel codeRel excpRel localsRel
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
  have firstBound' := firstBound.trans (Nat.mul_le_mul_right (controlSteps a source) leftSize)
  rw [compileProgExactHOLW,CrepSteps.steps_seq,targetRun]
  cases firstResult with
  | none =>
    obtain ⟨rfl,postLocals⟩ := resultRel
    simp only
    have secondBound := bBound middle sourceFinal result targetPost seqRun nonerror postState postCode postExcp postLocals
    have secondBound' := secondBound.trans (Nat.mul_le_mul_right (controlSteps b middle) rightSize)
    simp only at sourceCount
    simp only [compileProgExactHOLW] at firstBound' secondBound'
    simp only [CrepSteps.statementWeight]
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
      simp only [compileProgExactHOLW] at firstBound'
      simp only [CrepSteps.statementWeight]
      nlinarith


/-- Loop composition for the structural induction. -/
private theorem programBound_while {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : ExpHOL width) (body : ProgHOL width)
    (conditionShape : FrontendScalar context condition) (bodyShape : FrontendProgram context body)
    (bodyBound : ProgramBound context body) : ProgramBound context (.while condition body) := by
  intro σ source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
  have localised : localisedProgHOL (.while condition body) = true :=
    frontendProgram_localised (.while conditionShape bodyShape)
  have bounded := while_compiled_steps_compositional condition body context conditionShape
    (CrepSteps.statementWeight (compileProgExactHOLW context body))
    (CrepSteps.statementWeight_pos _) (by
      intro bs bf br bt hrun hgood hstate hcode hexcp hlocals _
      exact bodyBound bs bf br bt hrun hgood hstate hcode hexcp hlocals)
    source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel localised
  obtain ⟨ce,compiled⟩ := frontendWhile_compile context condition body conditionShape
  have sizeBound : CrepSteps.statementWeight (compileProgExactHOLW context body) ≤
      CrepSteps.statementWeight (compileProgExactHOLW context (.while condition body)) := by
    rw [compiled]
    simp only [CrepSteps.statementWeight]
    omega
  exact bounded.trans (Nat.mul_le_mul_right _ sizeBound)


/-- Conditional composition for the structural induction. -/
private theorem programBound_ite {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (condition : ExpHOL width) (a b : ProgHOL width)
    (conditionShape : FrontendScalar context condition)
    (aBound : ProgramBound context a) (bBound : ProgramBound context b) :
    ProgramBound context (.ite condition a b) := by
  classical
  intro σ source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
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
    have bound := bBound source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
    have scaled := bound.trans (Nat.mul_le_mul_right (controlSteps b source) rightSize)
    rw [comp] at scaled
    simp only [CrepSteps.statementWeight]
    nlinarith
  · simp only [if_neg zero] at run
    simp only [if_pos zero] at sourceCount ⊢
    have bound := aBound source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
    have scaled := bound.trans (Nat.mul_le_mul_right (controlSteps a source) leftSize)
    rw [comp] at scaled
    simp only [CrepSteps.statementWeight]
    nlinarith


/-- Declaration composition for the structural induction. -/
private theorem programBound_decl {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS) (initializer : ExpHOL width) (body : ProgHOL width)
    (initializerShape : FrontendScalar context initializer)
    (bodyBound : ProgramBound (scalarDeclContext context name) body) :
    ProgramBound context (.dec name .one initializer body) := by
  classical
  intro σ source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
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
        have bound := bodyBound _ bodyFinal bodyResult _ bodyRun nonerror innerState
          (by simpa [codeRelExactHOLW,scalarDeclContext,PanSemStateFiniteExact.setVarHOLFinite,CrepSemHOLState.setVar] using codeRel)
          (by simpa [scalarDeclContext,PanSemStateFiniteExact.setVarHOLFinite] using excpRel) innerLocals'
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
        have scaled := bound.trans (Nat.mul_le_mul_right
          (controlSteps body (PanSemStateFiniteExact.setVarHOLFinite name (.val word) source)) childSize)
        rw [comp,CrepSteps.steps_dec,hce,count]
        rw [comp] at scaled
        simp only
        simp only [CrepSteps.statementWeight]
        nlinarith
      | rStruct fields => simp [shapeOfHOLExact] at shape
      | nStruct name fields => simp [shapeOfHOLExact] at shape
    · rw [if_neg valid] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror


/-- Loop-free programs are the base cases of the structural induction. -/
private theorem programBound_static {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {program : ProgHOL width}
    (shape : FrontendProgram context program) (loopFree : noWhile program = true) :
    ProgramBound context program := by
  intro σ source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel
  have static := CrepSteps.staticProgram_statementWeight (frontendLoopFree_static shape loopFree) target
  have positive := controlSteps_pos program source
  nlinarith

private theorem frontendProgramBound {width : Nat} [NeZero width]
    {context : PanToCrepContextExact width} {program : ProgHOL width}
    (shape : FrontendProgram context program) : ProgramBound context program := by
  induction shape with
  | skip => exact programBound_static .skip rfl
  | «break» => exact programBound_static .break rfl
  | «continue» => exact programBound_static .continue rfl
  | tick => exact programBound_static .tick rfl
  | store a v => exact programBound_static (.store a v) rfl
  | assign reg found e => exact programBound_static (.assign reg found e) rfl
  | decl e body ih => exact programBound_decl _ _ _ _ e ih
  | seq a b iha ihb => exact programBound_seq _ _ _ a iha ihb
  | ite condition a b iha ihb => exact programBound_ite _ _ _ _ condition iha ihb
  | «while» condition body ih => exact programBound_while _ _ _ condition body ih
  | ret e => exact programBound_static (.ret e) rfl

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
  exact frontendProgramBound shape source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel


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
    (1 + sizeOf (compileProgExactHOLW context body)) (by omega) ?_ source sourceFinal result target
    run nonerror stateRel codeRel excpRel localsRel localised
  intro bs bf br bt _ _ _ _ _ _ _
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

/-- Source evaluation retains the function table across every outcome. -/
theorem source_code_preserved {width : Nat} [NeZero width] {σ : Type}
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ) (r : Option (PanSemResultExact width))
    (run : s.evaluateHOLFiniteState p = (r,t)) : t.code = s.code := by
  have h := evaluateInvariantsHOLFinite p (PanPropsEvalStateFiniteExact.ofPanSemFinite s) r
    (PanPropsEvalStateFiniteExact.ofPanSemFinite t) (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,run])
  exact h.2.2.2.2.2.2.1

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

/-- Zero clock prevents a Crep tail call from entering a callee. -/
theorem crep_call_zero_steps {width : Nat} [NeZero width] {σ : Type}
    (fname : MlS) (args : List (CrepExpHOL width)) (target : CrepSemHOLState width σ)
    (clock : target.clock = 0) : CrepSteps.steps (.call none fname args) target = 1 := by
  rw [CrepSteps.steps.eq_def]
  cases hargs : args.mapM (evalCrepSemHOLExp target) with
  | none => simp [hargs]
  | some vals =>
    cases hfind : target.code.lookup fname with
    | none => simp [hargs,hfind]
    | some entry =>
      obtain ⟨params,body⟩ := entry
      simp [hargs,hfind,clock]

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
    (programs : List (MlS × List Nat × CrepProgHOL width))
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
        CrepSteps.codeWeight programs * controlSteps body (PanSemStateFiniteExact.callEntryStateHOLFinite source locals)) :
    CrepSteps.steps (compileProgExactHOLW ctxt (.call none fname argexps)) target ≤
      CrepSteps.codeWeight programs * controlSteps (.call none fname argexps) source := by
  by_cases clock : source.clock = 0
  · have targetClock : target.clock = 0 := stateRel.2.2.2.2.2.1.symm.trans clock
    have count := crep_call_zero_steps fname ((compileExpExactHOLWList ctxt argexps).flatMap Prod.fst) target targetClock
    have sourcePositive := controlSteps_pos (.call none fname argexps) source
    have weightPositive : ∀ ps : List (MlS × List Nat × CrepProgHOL width), 1 ≤ CrepSteps.codeWeight ps := by
      intro ps
      induction ps with
      | nil => simp [CrepSteps.codeWeight]
      | cons row rest ih =>
        change 1 ≤ max (CrepSteps.statementWeight row.2.2) (CrepSteps.codeWeight rest)
        exact Nat.le_trans ih (Nat.le_max_right _ _)
    have weightPositive := weightPositive programs
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
    have positive : 1 ≤ CrepSteps.codeWeight programs := by
      have w := SteppedFlapjack.CrepToLoopSteps.lookup_statementWeight_le_codeWeight programs fname
        (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))
        (compileProgExactHOLW (ctxtFcExactHOL ctxt.funcs ctxt.eids (shapes.map Prod.fst) (shapes.map Prod.snd)
          (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))) body) (by simpa [code] using htgt)
      have p := CrepSteps.statementWeight_pos (compileProgExactHOLW (ctxtFcExactHOL ctxt.funcs ctxt.eids
        (shapes.map Prod.fst) (shapes.map Prod.snd) (List.range (sizeOfShapeHOL (.comb (shapes.map Prod.snd))))) body)
      omega
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
  have b := bodyIH shapes hsrc htgt smaller hlocal bs bc be bl
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
  have b := bodyIH shapes hsrc htgt smaller hlocal bs bc be bl
  have overhead : (decCallSlots ctxt shape).length + 2 ≤ K := by
    rw [decCall_statementWeight] at weight
    simp [decCallSlots]
    omega
  rw [hsource,htarget]
  nlinarith

end SteppedFlapjack.PanToCrepSteps
