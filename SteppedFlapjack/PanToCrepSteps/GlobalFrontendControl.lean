import SteppedFlapjack.PanToCrepSteps.GlobalFrontend
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def GlobalControl (globals : PanGlobalsContextExact 64) (p : ProgHOL 64) : Prop :=
  ∀ {σ : Type} (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    source.evaluateHOLFiniteState p = (result,sourceFinal) → result ≠ some .error →
    panGlobalsStateRelHOLExact true globals source target →
    controlSteps (compileProgExactHOL globals p) target = controlSteps p source

private theorem controlSeq {g : PanGlobalsContextExact 64} {a b : ProgHOL 64}
    (ha : GlobalControl g a) (hb : GlobalControl g b) : GlobalControl g (.seq a b) := by
  intro σ source sourceFinal target result run nonerror rel
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases firstRun : source.evaluateHOLFiniteState a with ⟨firstResult,middle⟩
  rw [firstRun] at run
  dsimp only at run
  have firstNonerror : firstResult ≠ some .error := by
    intro h
    rw [h] at run
    exact nonerror (Prod.mk.inj run).1.symm
  obtain ⟨targetMiddle,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    a source firstResult g target middle ⟨rel,firstRun,firstNonerror⟩
  have firstCost := ha source middle target firstResult firstRun firstNonerror rel
  simp only [compileProgExactHOL]
  rw [controlSteps_seq,controlSteps_seq,firstRun,targetRun]
  cases firstResult with
  | none =>
    simp only [goodResHOL] at postRel
    have secondCost := hb middle sourceFinal targetMiddle result run nonerror postRel
    simp only [secondCost,firstCost]
  | some r => simp only [firstCost]

private theorem controlIte {g : PanGlobalsContextExact 64} {condition : ExpHOL 64} {a b : ProgHOL 64}
    (ha : GlobalControl g a) (hb : GlobalControl g b) : GlobalControl g (.ite condition a b) := by
  classical
  intro σ source sourceFinal target result run nonerror rel
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition
    (.val (.word w)) g target ⟨rel,heval⟩
  change @evalHOLExact 64 σ _ target.toExact (fun a => Classical.propDecidable (target.memaddrs a))
    (compileExpExactHOL g condition) = some (.val (.word w)) at targetEval
  simp only [compileProgExactHOL]
  rw [controlSteps_ite,controlSteps_ite]
  simp only [heval,targetEval]
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false]
    rw [hb source sourceFinal target result run nonerror rel]
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    rw [ha source sourceFinal target result run nonerror rel]
private theorem controlDecl {g : PanGlobalsContextExact 64} (name : MlS) {initializer : ExpHOL 64} {body : ProgHOL 64}
    (bodyBound : GlobalControl g body) : GlobalControl g (.dec name .one initializer body) := by
  intro σ source sourceFinal target result run nonerror rel
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases evaluated : @evalHOLExact 64 σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [evaluated] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    simp only [evaluated] at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · simp only [valid,ite_true] at run
      have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source initializer value g target ⟨rel,evaluated⟩
      have bodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL g source target true name value rel
      rcases bodyRun : (setVarHOLFinite name value source).evaluateHOLFiniteState body with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bound := bodyBound _ bodyFinal _ bodyResult bodyRun nonerror bodyRel
      simp only [compileProgExactHOL]
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid,
        controlSteps_dec _ _ _ _ _ value targetEval valid, bound]
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror
private theorem controlWhile {g : PanGlobalsContextExact 64} {condition : ExpHOL 64} {body : ProgHOL 64}
    (bodyBound : GlobalControl g body) : GlobalControl g (.while condition body) := by
  classical
  intro σ source sourceFinal target result run nonerror rel
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result target with
  | _ clock ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have ht := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition (.val (.word w)) g target ⟨rel,heval⟩
    have hevalExact : @evalHOLExact 64 σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) condition = some (.val (.word w)) := heval
    have htExact : @evalHOLExact 64 σ _ target.toExact
        (fun a => Classical.propDecidable (target.memaddrs a)) (compileExpExactHOL g condition) = some (.val (.word w)) := ht
    have sourceCount := controlSteps_while condition body source
    simp only [compileProgExactHOL]
    rw [controlSteps_while]
    simp only [hevalExact] at sourceCount
    simp only [htExact]
    have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
    by_cases nz : w ≠ 0
    · by_cases z : source.clock = 0
      · have tz : target.clock = 0 := clockRel ▸ z
        simp only [tz,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero]
        simp only [z,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero] at sourceCount
        exact sourceCount.symm
      · have tz : target.clock ≠ 0 := clockRel ▸ z
        simp only [if_pos (show w ≠ 0 ∧ target.clock ≠ 0 from ⟨nz,tz⟩)]
        rw [if_pos nz,if_neg z] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState body with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyRel := PanGlobalsStateRelationClock.stateRelDecClockHOL g source target true rel
        obtain ⟨targetPost,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL body
          source.decClockHOLFinite bodyResult g target.decClockHOLFinite sourcePost ⟨bodyRel,bodyRun,bodyNonerror⟩
        rw [targetRun]
        have bodyCost := bodyBound source.decClockHOLFinite sourcePost target.decClockHOLFinite bodyResult bodyRun bodyNonerror bodyRel
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result (by simpa using run) nonerror postRel rfl
          simp only [compileProgExactHOL] at recurse
          simp only at sourceCount ⊢
          rw [bodyCost,recurse,← sourceCount]
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result (by simpa using run) nonerror postRel rfl
            simp only [compileProgExactHOL] at recurse
            simp only at sourceCount ⊢
            rw [bodyCost,recurse,← sourceCount]
          | error => exact absurd rfl bodyNonerror
          | «break» | timeOut | returned _ | finalFfi _ | exception _ _ =>
            simp only [Nat.add_zero]
            simp only at sourceCount
            rw [bodyCost]
            simpa only [Nat.add_zero] using sourceCount.symm
    · have tz : ¬ (w ≠ 0 ∧ target.clock ≠ 0) := fun h => nz h.1
      have sz : ¬ (w ≠ 0 ∧ source.clock ≠ 0) := fun h => nz h.1
      simp only [if_neg tz,Nat.add_zero]
      simp only [if_neg sz,Nat.add_zero] at sourceCount
      exact sourceCount.symm
/-- Global lowering preserves exact control visits for the supported call-free
    fragment, including loops that read and update globals. -/
theorem globalFrontend_controlSteps {g : PanGlobalsContextExact 64} {ctxt : PanToCrepContextExact 64}
    {p : ProgHOL 64} (shape : GlobalFrontend g ctxt p) : GlobalControl g p := by
  induction shape with
  | skip | store | assignLocal | ret =>
    intro σ source sourceFinal target result run nonerror rel
    simp [compileProgExactHOL,controlSteps.eq_def]
  | assignGlobal found e =>
    intro σ source sourceFinal target result run nonerror rel
    simp [compileProgExactHOL,found,controlSteps.eq_def]
  | assignGlobalStruct found e =>
    intro σ source sourceFinal target result run nonerror rel
    simp [compileProgExactHOL,found,controlSteps.eq_def]
  | decl e body ih => exact controlDecl _ ih
  | seq a b iha ihb => exact controlSeq iha ihb
  | ite e a b iha ihb => exact controlIte iha ihb
  | «while» e body ih => exact controlWhile ih
/-- A source-visit budget carries through global lowering and Crep with a
    bound computed from the actual generated code. -/
theorem globalFrontend_correct_with_steps {σ : Type}
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : GlobalFrontend globals ctxt p)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (crep : CrepSemHOLState 64 σ) (sourceLimit : Nat)
    (run : source.evaluateHOLFiniteState p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (sourceBound : controlSteps p source ≤ sourceLimit)
    (globalRel : panGlobalsStateRelHOLExact true globals source target)
    (stateRel : panToCrepStateRelFiniteExact target crep)
    (codeRel : codeRelExactHOLW ctxt target.code crep.code)
    (excpRel : panToCrepExcpRelFiniteExact ctxt.eids target.eshapes)
    (localsRel : panToCrepLocalsRelFiniteExact ctxt target.locals crep.locals) :
    ∃ targetFinal crepResult crepFinal,
      target.evaluateHOLFiniteState (compileProgExactHOL globals p) = (result,targetFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL result) globals sourceFinal targetFinal ∧
      evalCrepSemHOLProgExact crep (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) = (crepResult,crepFinal) ∧
      panToCrepStateRelFiniteExact targetFinal crepFinal ∧
      pcCompileCorrectResultRel ctxt targetFinal crepFinal result crepResult ∧
      SteppedFlapjack.CrepSteps.steps (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) crep ≤
        SteppedFlapjack.CrepSteps.statementWeight (compileProgExactHOLW ctxt (compileProgExactHOL globals p)) * sourceLimit := by
  obtain ⟨targetFinal,targetRun,globalFinal⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
      p source result globals target sourceFinal ⟨globalRel,run,nonerror⟩
  have control := globalFrontend_controlSteps shape source sourceFinal target result run nonerror globalRel
  have loweredBound : controlSteps (compileProgExactHOL globals p) target ≤ sourceLimit := by
    rw [control]
    exact sourceBound
  obtain ⟨crepResult,crepFinal,crepRun,finalRel,_,_,resultRel,steps⟩ := frontend_correct_with_steps
    ctxt (compileProgExactHOL globals p) (globalFrontend_compiled shape) target targetFinal result crep
    sourceLimit targetRun nonerror loweredBound stateRel codeRel excpRel localsRel
  exact ⟨targetFinal,crepResult,crepFinal,targetRun,globalFinal,crepRun,finalRel,resultRel,steps⟩
end SteppedFlapjack.PanToCrepSteps
