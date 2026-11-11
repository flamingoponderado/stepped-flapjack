import SteppedFlapjack.Concrete.FrontendShape
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

private def GlobalControl (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (globals : PanGlobalsContextExact 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal) → result ≠ some .error →
    panGlobalsStateRelHOLExact true globals source target →
    controlSteps (progToHOL program) target = controlSteps (progToHOL program) source

private theorem globalSeq {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (ashape : CallSupportedIn scope a) (aBound : GlobalControl a) (bBound : GlobalControl b) : GlobalControl (.seq a b) := by
  intro σ globals source sourceFinal target result run nonerror rel
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
  have firstCost := aBound globals source middle target firstResult firstRun firstNonerror rel
  rw [controlSteps_seq,controlSteps_seq,firstRun,targetRun]
  cases firstResult with
  | none =>
    simp only [goodResHOL] at postRel
    have secondCost := bBound globals middle sourceFinal targetMiddle result run nonerror postRel
    simp only [secondCost,firstCost]
  | some r => simp only [firstCost]

private theorem globalDecl {scope : List VarName} (name : VarName)
    {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyBound : GlobalControl body) :
    GlobalControl (.dec name .one initializer body) := by
  intro σ globals source sourceFinal target result run nonerror rel
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
      have bound := bodyBound globals _ bodyFinal _ bodyResult bodyRun nonerror bodyRel
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid,
        controlSteps_dec _ _ _ _ _ value targetEval valid, bound]
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

private theorem globalIte {scope : List VarName} {condition : Exp (RiscV.Word 64)}
    {a b : Prog (RiscV.Word 64)} (scalar : Scalar scope condition)
    (aBound : GlobalControl a) (bBound : GlobalControl b) : GlobalControl (.ite condition a b) := by
  classical
  intro σ globals source sourceFinal target result run nonerror rel
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
    rw [bBound globals source sourceFinal target result run nonerror rel]
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    rw [aBound globals source sourceFinal target result run nonerror rel]

private theorem globalWhile {scope : List VarName} {condition : Exp (RiscV.Word 64)}
    {body : Prog (RiscV.Word 64)} (scalar : Scalar scope condition)
    (bodyShape : CallSupportedIn scope body) (bodyBound : GlobalControl body) :
    GlobalControl (.while condition body) := by
  classical
  intro σ globals source sourceFinal target result run nonerror rel
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
        have bodyCost := bodyBound globals source.decClockHOLFinite sourcePost target.decClockHOLFinite bodyResult bodyRun bodyNonerror bodyRel
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result nonerror postRel (by simpa using run) rfl
          simp only at sourceCount ⊢
          rw [bodyCost,recurse,← sourceCount]
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result nonerror postRel (by simpa using run) rfl
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

/-- The reached-tail-call visit step, parameterized by the callee induction hypothesis. -/
private theorem globalTailReached {scope calleeScope : List VarName} {σ : Type}
    (function : FunName) (args : List (Exp (RiscV.Word 64))) (argShape : ∀ e ∈ args, Scalar scope e)
    (callee : Prog (RiscV.Word 64)) (calleeShape : CallSupportedIn calleeScope callee)
    (globals : PanGlobalsContextExact 64) (source sourceFinal target : PanSemStateFiniteExact 64 σ)
    (result : Option (PanSemResultExact 64)) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (sourceArgs : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a))
      (args.map expToHOL) = some values)
    (sourceFound : lookupCodeHOLFinite source.code.lookup (Flapjack.Basis.Pure.MlString.ofString function) values =
      some (progToHOL callee,locals,returnShape)) (clock : source.clock ≠ 0)
    (run : source.evaluateHOLFiniteState (progToHOL (.call none function args)) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target)
    (calleeBound : ∀ bodyResult bodyFinal,
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState (progToHOL callee) = (bodyResult,bodyFinal) →
      bodyResult ≠ some .error →
      panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) →
      controlSteps (progToHOL callee) (callEntryStateHOLFinite target locals) =
        controlSteps (progToHOL callee) (callEntryStateHOLFinite source locals)) :
    controlSteps (progToHOL (.call none function args)) target = controlSteps (progToHOL (.call none function args)) source := by
  have argFixed : (args.map expToHOL).map (compileExpExactHOL globals) = args.map expToHOL := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e member
    exact scalar_globals_fixed (argShape e member) globals
  have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL globals source target (args.map expToHOL) values ⟨rel,sourceArgs⟩
  rw [argFixed] at targetArgs
  have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL globals source target true
    (Flapjack.Basis.Pure.MlString.ofString function) values (progToHOL callee) locals returnShape ⟨rel,sourceFound⟩
  rw [callSupportedIn_globals_fixed calleeShape globals] at targetFound
  have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
  have targetClock : target.clock ≠ 0 := clockRel ▸ clock
  have decremented := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
  have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals source.decClockHOLFinite
    target.decClockHOLFinite true locals).1 decremented
  change panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) at entryRel
  rcases bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState (progToHOL callee) with ⟨bodyResult,bodyFinal⟩
  have bodyNonerror : bodyResult ≠ some .error := by
    intro bad
    simp only [progToHOL,evaluateHOLFiniteState_call,sourceArgs,sourceFound,if_neg clock,bodyRun,bad] at run
    exact nonerror (Prod.mk.inj run).1.symm
  have equal := calleeBound bodyResult bodyFinal bodyRun bodyNonerror entryRel
  simp only [progToHOL]
  rw [controlSteps_tailCall _ _ source values (progToHOL callee) locals returnShape sourceArgs sourceFound clock,
    controlSteps_tailCall _ _ target values (progToHOL callee) locals returnShape targetArgs targetFound targetClock,equal]

/-- Global lowering preserves control visits for all supported programs,
including arbitrarily nested control flow. -/
private theorem supportedIn_globalControl {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : GlobalControl program := by
  induction supported with
  | skip | assign | ret =>
    intro σ globals source sourceFinal target result run nonerror rel
    simp [progToHOL,controlSteps.eq_def]
  | decl name scalar body ih => exact globalDecl name scalar ih
  | seq a b iha ihb => exact globalSeq (.base a) iha ihb
  | ite scalar a b iha ihb => exact globalIte scalar iha ihb
  | «while» scalar body ih => exact globalWhile scalar (.base body) ih

/-- A non-error supported run has the same number of control visits after
global lowering, including every reached iteration of nested loops. -/
theorem supported_globals_control {σ : Type} {program : Prog (RiscV.Word 64)}
    (supported : Supported program) (globals : PanGlobalsContextExact 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target) :
    controlSteps (progToHOL program) target = controlSteps (progToHOL program) source :=
  supportedIn_globalControl supported.1 globals source sourceFinal target result run nonerror rel

end SteppedFlapjack.Concrete
