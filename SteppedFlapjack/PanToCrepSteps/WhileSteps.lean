import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.PanToCrepSteps.FrontendProgram

/-! Quantitative correctness of Pancake while compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- For a non-error source run, the actual compiled Crep while visits at most
one plus the compiled body size per Pancake control visit. -/
private theorem while_compiled_steps_compositional {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (context : PanToCrepContextExact width)
    (conditionShape : FrontendScalar context condition)
    (bodyFactor : Nat)
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
      (1 + bodyFactor) * controlSteps (.while condition body) source := by
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
              (1 + bodyFactor) * controlSteps (.while condition body) source := by
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
    (CrepSteps.statementWeight (compileProgExactHOLW context body)) (by
      intro bs bf br bt hrun hgood hstate hcode hexcp hlocals _
      exact bodyBound bs bf br bt hrun hgood hstate hcode hexcp hlocals)
    source sourceFinal result target run nonerror stateRel codeRel excpRel localsRel localised
  obtain ⟨ce,compiled⟩ := frontendWhile_compile context condition body conditionShape
  have sizeBound : 1 + CrepSteps.statementWeight (compileProgExactHOLW context body) ≤
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
    (sizeOf (compileProgExactHOLW context body)) ?_ source sourceFinal result target
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


end SteppedFlapjack.PanToCrepSteps
