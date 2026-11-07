import SteppedFlapjack.Concrete.SimpRun
import SteppedFlapjack.PanToCrepSteps.ControlSteps
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps Flapjack.Basis.Pure.MlString

private def CodeControl (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source sourceFinal : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (result : Option (PanSemResultExact 64)),
    source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal) → result ≠ some .error →
    PanSimp.CodeRel source.code code →
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source

private theorem codeSeq {a b : Prog (RiscV.Word 64)}
    (aBound : CodeControl a) (bBound : CodeControl b) : CodeControl (.seq a b) := by
  intro σ source sourceFinal code result run nonerror codeRel
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases firstRun : source.evaluateHOLFiniteState (progToHOL a) with ⟨firstResult,middle⟩
  rw [firstRun] at run
  dsimp only at run
  have firstNonerror : firstResult ≠ some .error := by
    intro h
    rw [h] at run
    exact nonerror (Prod.mk.inj run).1.symm
  have sim := PanSimp.codeSimAll (progToHOL a) source firstResult middle code firstRun firstNonerror codeRel
  obtain ⟨targetRun,codePreserved⟩ := sim
  have firstCost := aBound source middle code firstResult firstRun firstNonerror codeRel
  rw [controlSteps_seq,controlSteps_seq,firstRun,targetRun]
  cases firstResult with
  | none =>
    have nextRel : PanSimp.CodeRel middle.code code := by simpa [codePreserved] using codeRel
    have secondCost := bBound middle sourceFinal code result run nonerror nextRel
    simp only [secondCost,firstCost]
  | some r => simp only [firstCost]

private theorem codeDecl (name : VarName)
    {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (bodyBound : CodeControl body) : CodeControl (.dec name .one initializer body) := by
  classical
  intro σ source sourceFinal code result run nonerror codeRel
  simp only [progToHOL,shapeToHOL] at run ⊢
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases evaluated : @evalHOLExact 64 σ _ source.toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
  | none =>
    simp only [evaluated] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    simp only [evaluated] at run
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · simp only [valid,ite_true] at run
      have targetEval : @evalHOLExact 64 σ _ ({source with code := code} : PanSemStateFiniteExact 64 σ).toExact
          (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) = some value := by
        change @evalHOLExact 64 σ _ {source.toExact with code := code.lookup}
          (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) = some value
        rw [evalHOLExact_upd_code_eq]
        exact evaluated
      rcases bodyRun : (setVarHOLFinite (ofString name) value source).evaluateHOLFiniteState
          (progToHOL body) with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bodyRel : PanSimp.CodeRel (setVarHOLFinite (ofString name) value source).code code := codeRel
      have bound := bodyBound (setVarHOLFinite (ofString name) value source) bodyFinal code bodyResult bodyRun nonerror bodyRel
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid,
        controlSteps_dec _ _ _ _ _ value targetEval valid]
      simpa only [setVarHOLFinite] using congrArg (1 + ·) bound
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

private theorem codeIte {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (aBound : CodeControl a) (bBound : CodeControl b) : CodeControl (.ite condition a b) := by
  classical
  intro σ source sourceFinal code result run nonerror codeRel
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  have targetEval : @evalHOLExact 64 σ _ ({source with code := code} : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := by
    change @evalHOLExact 64 σ _ {source.toExact with code := code.lookup}
      (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w))
    rw [evalHOLExact_upd_code_eq]
    exact heval
  rw [controlSteps_ite,controlSteps_ite]
  simp only [heval,targetEval]
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false]
    rw [bBound source sourceFinal code result run nonerror codeRel]
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    rw [aBound source sourceFinal code result run nonerror codeRel]

private theorem codeWhile {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (bodyBound : CodeControl body) : CodeControl (.while condition body) := by
  classical
  intro σ source sourceFinal code result run nonerror codeRel
  simp only [progToHOL] at run ⊢
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result with
  | _ clock ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have hevalExact : @evalHOLExact 64 σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := heval
    have targetEval : @evalHOLExact 64 σ _ ({source with code := code} : PanSemStateFiniteExact 64 σ).toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := by
      change @evalHOLExact 64 σ _ {source.toExact with code := code.lookup}
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w))
      rw [evalHOLExact_upd_code_eq]
      exact hevalExact
    have sourceCount := controlSteps_while (expToHOL condition) (progToHOL body) source
    rw [controlSteps_while]
    simp only [hevalExact] at sourceCount
    simp only [← hc]
    simp only [targetEval]
    by_cases nz : w ≠ 0
    · by_cases z : source.clock = 0
      · simp only [z,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero] at sourceCount ⊢
        exact sourceCount.symm
      · simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩)]
        rw [if_pos nz,if_neg z] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyRel : PanSimp.CodeRel source.decClockHOLFinite.code code := codeRel
        obtain ⟨targetRun,codePreserved⟩ := PanSimp.codeSimAll (progToHOL body) source.decClockHOLFinite
          bodyResult sourcePost code bodyRun bodyNonerror bodyRel
        have targetRun' : ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState
            (progToHOL body) = (bodyResult,{sourcePost with code := code}) := by
          simpa only [decClockHOLFinite] using targetRun
        rw [targetRun']
        have bodyCost := bodyBound source.decClockHOLFinite sourcePost code bodyResult bodyRun bodyNonerror bodyRel
        have bodyCost' : controlSteps (progToHOL body) ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite =
            controlSteps (progToHOL body) source.decClockHOLFinite := by simpa only [decClockHOLFinite] using bodyCost
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        have postRel : PanSimp.CodeRel sourcePost.code code := by simpa [codePreserved,decClockHOLFinite] using codeRel
        simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result nonerror postRel (by simpa using run) rfl
          simp only at sourceCount ⊢
          rw [bodyCost',recurse,← sourceCount]
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result nonerror postRel (by simpa using run) rfl
            simp only at sourceCount ⊢
            rw [bodyCost',recurse,← sourceCount]
          | error => exact absurd rfl bodyNonerror
          | «break» | timeOut | returned _ | finalFfi _ | exception _ _ =>
            simp only [Nat.add_zero]
            simp only at sourceCount
            rw [bodyCost']
            simpa only [Nat.add_zero] using sourceCount.symm
    · have sz : ¬ (w ≠ 0 ∧ source.clock ≠ 0) := fun h => nz h.1
      simp only [if_neg sz,Nat.add_zero]
      simp only [if_neg sz,Nat.add_zero] at sourceCount
      exact sourceCount.symm

private theorem supportedCodeControl {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : CodeControl program := by
  induction supported with
  | skip | assign | ret =>
    intro σ source sourceFinal code result run nonerror codeRel
    simp [progToHOL,controlSteps.eq_def]
  | decl name scalar body ih => exact codeDecl name ih
  | seq a b iha ihb => exact codeSeq iha ihb
  | ite scalar a b iha ihb => exact codeIte iha ihb
  | «while» scalar body ih => exact codeWhile ih

/-- Replacing the code table with the actual pan_simp output preserves the
control visits of any non-error supported source run. -/
theorem supported_panSimp_code_control {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (sourceCode : source.code = HolFiniteMapExact.empty.update (entryName (progToHOL program),([],progToHOL program,.one)))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) (nonerror : result ≠ some .error) :
    controlSteps (progToHOL program) (panSimpSourceState program source) = controlSteps (progToHOL program) source := by
  have relation := supported_panSimp_state_rel program supported source sourceCode
  have codeRel : PanSimp.CodeRel source.code (panSimpSourceState program source).code := relation.2
  exact supportedCodeControl supported.1 source sourceFinal _ result run nonerror codeRel

end SteppedFlapjack.Concrete
