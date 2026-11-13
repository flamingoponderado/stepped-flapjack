import SteppedFlapjack.Concrete.FrontendShape
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

private def GlobalControl (P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop) (limit : Nat) (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (globals : PanGlobalsContextExact 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    source.clock ≤ limit → P source.code → source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal) → result ≠ some .error →
    panGlobalsStateRelHOLExact true globals source target →
    controlSteps (progToHOL program) target = controlSteps (progToHOL program) source

private theorem globalSeq {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (ashape : CallSupportedIn scope a) (aBound : GlobalControl P limit a) (bBound : GlobalControl P limit b) : GlobalControl P limit (.seq a b) := by
  intro σ globals source sourceFinal target result budget tableInvariant run nonerror rel
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases firstRun : source.evaluateHOLFiniteState (progToHOL a) with ⟨firstResult,middle⟩
  rw [firstRun] at run
  dsimp only at run
  have firstNonerror : firstResult ≠ some .error := by
    intro h
    rw [h] at run
    exact nonerror (Prod.mk.inj run).1.symm
  obtain ⟨targetMiddle,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (progToHOL a) source firstResult globals target middle ⟨rel,firstRun,firstNonerror⟩
  rw [callSupportedIn_globals_fixed ashape globals] at targetRun
  have firstCost := aBound globals source middle target firstResult budget tableInvariant firstRun firstNonerror rel
  rw [controlSteps_seq,controlSteps_seq,firstRun,targetRun]
  cases firstResult with
  | none =>
    simp only [goodResHOL] at postRel
    have middleBudget : middle.clock ≤ limit := by
      have h := evaluateHOLFiniteState_clock_le source (progToHOL a)
      rw [firstRun] at h
      simp only at h
      omega
    have middleCode : middle.code = source.code := by
      have h := SemInitSupport.eval_code source (progToHOL a)
      rw [firstRun] at h
      exact h
    have middleTable : P middle.code := by rw [middleCode]; exact tableInvariant
    have secondCost := bBound globals middle sourceFinal targetMiddle result middleBudget middleTable run nonerror postRel
    simp only [secondCost,firstCost]
  | some r => simp only [firstCost]

private theorem globalDecl {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {scope : List VarName} (name : VarName)
    {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyBound : GlobalControl P limit body) :
    GlobalControl P limit (.dec name .one initializer body) := by
  intro σ globals source sourceFinal target result budget tableInvariant run nonerror rel
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
      have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source (expToHOL initializer) value globals target ⟨rel,evaluated⟩
      rw [scalar_globals_fixed scalar globals] at targetEval
      have bodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL globals source target true (Flapjack.Basis.Pure.MlString.ofString name) value rel
      rcases bodyRun : (setVarHOLFinite (Flapjack.Basis.Pure.MlString.ofString name) value source).evaluateHOLFiniteState
          (progToHOL body) with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bodyBudget : (setVarHOLFinite (Flapjack.Basis.Pure.MlString.ofString name) value source).clock ≤ limit := by
        simpa [setVarHOLFinite] using budget
      have bodyTable : P (setVarHOLFinite (Flapjack.Basis.Pure.MlString.ofString name) value source).code := by
        simpa [setVarHOLFinite] using tableInvariant
      have bound := bodyBound globals _ bodyFinal _ bodyResult bodyBudget bodyTable bodyRun nonerror bodyRel
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid,
        controlSteps_dec _ _ _ _ _ value targetEval valid, bound]
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

private theorem globalIte {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {scope : List VarName} {condition : Exp (RiscV.Word 64)}
    {a b : Prog (RiscV.Word 64)} (scalar : Scalar scope condition)
    (aBound : GlobalControl P limit a) (bBound : GlobalControl P limit b) : GlobalControl P limit (.ite condition a b) := by
  classical
  intro σ globals source sourceFinal target result budget tableInvariant run nonerror rel
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source (expToHOL condition)
    (.val (.word w)) globals target ⟨rel,heval⟩
  rw [scalar_globals_fixed scalar globals] at targetEval
  change @evalHOLExact 64 σ _ target.toExact (fun a => Classical.propDecidable (target.memaddrs a))
    (expToHOL condition) = some (.val (.word w)) at targetEval
  rw [controlSteps_ite,controlSteps_ite]
  simp only [heval,targetEval]
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false]
    rw [bBound globals source sourceFinal target result budget tableInvariant run nonerror rel]
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    rw [aBound globals source sourceFinal target result budget tableInvariant run nonerror rel]

private theorem globalWhile {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {scope : List VarName} {condition : Exp (RiscV.Word 64)}
    {body : Prog (RiscV.Word 64)} (scalar : Scalar scope condition)
    (bodyShape : CallSupportedIn scope body) (bodyBound : GlobalControl P limit body) :
    GlobalControl P limit (.while condition body) := by
  classical
  intro σ globals source sourceFinal target result budget tableInvariant run nonerror rel
  simp only [progToHOL] at run ⊢
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result target with
  | _ clock ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have ht := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source (expToHOL condition) (.val (.word w)) globals target ⟨rel,heval⟩
    rw [scalar_globals_fixed scalar globals] at ht
    have hevalExact : @evalHOLExact 64 σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := heval
    have htExact : @evalHOLExact 64 σ _ target.toExact
        (fun a => Classical.propDecidable (target.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := ht
    have sourceCount := controlSteps_while (expToHOL condition) (progToHOL body) source
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
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyRel := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
        obtain ⟨targetPost,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL (progToHOL body)
          source.decClockHOLFinite bodyResult globals target.decClockHOLFinite sourcePost ⟨bodyRel,bodyRun,bodyNonerror⟩
        rw [callSupportedIn_globals_fixed bodyShape globals] at targetRun
        rw [targetRun]
        have bodyBudget : source.decClockHOLFinite.clock ≤ limit := by simp only [decClockHOLFinite]; omega
        have bodyTable : P source.decClockHOLFinite.code := tableInvariant
        have bodyCost := bodyBound globals source.decClockHOLFinite sourcePost target.decClockHOLFinite bodyResult bodyBudget bodyTable bodyRun bodyNonerror bodyRel
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        have postBudget : sourcePost.clock ≤ limit := by omega
        have postCode : sourcePost.code = source.code := by
          have h := SemInitSupport.eval_code source.decClockHOLFinite (progToHOL body)
          rw [bodyRun] at h
          simpa [decClockHOLFinite] using h
        have postTable : P sourcePost.code := by rw [postCode]; exact tableInvariant
        simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result postBudget postTable nonerror postRel (by simpa using run) rfl
          simp only at sourceCount ⊢
          rw [bodyCost,recurse,← sourceCount]
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result postBudget postTable nonerror postRel (by simpa using run) rfl
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

/-- Global lowering preserves control visits for all supported programs,
including arbitrarily nested control flow. -/
private theorem supportedIn_globalControl {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop)
    (limit : Nat) : GlobalControl P limit program := by
  induction supported with
  | skip | store | assign | ret =>
    intro σ globals source sourceFinal target result budget tableInvariant run nonerror rel
    simp [progToHOL,controlSteps.eq_def]
  | decl name scalar body ih => exact globalDecl name scalar ih
  | seq a b iha ihb => exact globalSeq (.base a) iha ihb
  | ite scalar a b iha ihb => exact globalIte scalar iha ihb
  | «while» scalar body ih => exact globalWhile scalar (.base body) ih

/-- A non-error supported run has the same number of control visits after
global lowering, including every reached iteration of nested loops. -/
theorem supported_globals_control {σ : Type} {program : Prog (RiscV.Word 64)}
    (supported : CallFreeSupported program) (globals : PanGlobalsContextExact 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (progToHOL program) target = controlSteps (progToHOL program) source :=
  supportedIn_globalControl supported.1 (fun _ => True) source.clock globals source sourceFinal target result (Nat.le_refl _) trivial run nonerror rel

end SteppedFlapjack.Concrete
