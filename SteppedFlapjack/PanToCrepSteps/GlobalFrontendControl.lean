import SteppedFlapjack.PanToCrepSteps.GlobalFrontend
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationClock
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationLocals
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Every reachable source function belongs to the global call-aware fragment. -/
def GlobalCallTable (g : PanGlobalsContextExact 64)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ name values body locals rsh, lookupCodeHOLFinite code.lookup name values = some (body,locals,rsh) →
    ∃ ctxt, GlobalCallFrontend g ctxt body

private def Bound (g : PanGlobalsContextExact 64) (P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop) (limit : Nat) (p : ProgHOL 64) : Prop :=
  ∀ {σ : Type} (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    source.clock ≤ limit → P source.code →
    source.evaluateHOLFiniteState p = (result,sourceFinal) → result ≠ some .error →
    panGlobalsStateRelHOLExact true g source target →
    controlSteps (compileProgExactHOL g p) target = controlSteps p source

private theorem boundSeq {g : PanGlobalsContextExact 64} {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {a b : ProgHOL 64}
    (ha : Bound g P limit a) (hb : Bound g P limit b) : Bound g P limit (.seq a b) := by
  intro σ source sourceFinal target result budget table run nonerror rel
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
  have firstCost := ha source middle target firstResult budget table firstRun firstNonerror rel
  simp only [compileProgExactHOL]
  rw [controlSteps_seq,controlSteps_seq,firstRun,targetRun]
  cases firstResult with
  | none =>
    simp only [goodResHOL] at postRel
    have middleBudget : middle.clock ≤ limit := by
      have h := evaluateHOLFiniteState_clock_le source a
      rw [firstRun] at h
      simp only at h
      omega
    have middleCode : middle.code = source.code := by
      have h := SemInitSupport.eval_code source a
      rw [firstRun] at h
      exact h
    have middleTable : P middle.code := by rw [middleCode]; exact table
    have secondCost := hb middle sourceFinal targetMiddle result middleBudget middleTable run nonerror postRel
    simp only [secondCost,firstCost]
  | some r => simp only [firstCost]

private theorem boundIte {g : PanGlobalsContextExact 64} {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {condition : ExpHOL 64} {a b : ProgHOL 64}
    (ha : Bound g P limit a) (hb : Bound g P limit b) : Bound g P limit (.ite condition a b) := by
  classical
  intro σ source sourceFinal target result budget table run nonerror rel
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source condition (.val (.word w)) g target ⟨rel,heval⟩
  change @evalHOLExact 64 σ _ target.toExact (fun a => Classical.propDecidable (target.memaddrs a))
    (compileExpExactHOL g condition) = some (.val (.word w)) at targetEval
  simp only [compileProgExactHOL]
  rw [controlSteps_ite,controlSteps_ite]
  simp only [heval,targetEval]
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false]
    rw [hb source sourceFinal target result budget table run nonerror rel]
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    rw [ha source sourceFinal target result budget table run nonerror rel]

private theorem boundDecl {g : PanGlobalsContextExact 64} {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} (name : MlS) (declared : ShapeHOL) {initializer : ExpHOL 64} {body : ProgHOL 64}
    (bodyBound : Bound g P limit body) : Bound g P limit (.dec name declared initializer body) := by
  intro σ source sourceFinal target result budget table run nonerror rel
  rw [evaluateHOLFiniteState_dec_total] at run
  dsimp only at run
  cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) initializer with
  | none =>
    simp only [evaluated] at run
    exact absurd (Prod.mk.inj run).1.symm nonerror
  | some value =>
    simp only [evaluated] at run
    by_cases valid : shapeEqHOL declared (shapeOfHOLExact value) = true
    · simp only [valid,ite_true] at run
      have targetEval := PanGlobalsCompileExpCorrect.compileExpCorrectHOL source initializer value g target ⟨rel,evaluated⟩
      have bodyRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL g source target true name value rel
      rcases bodyRun : (setVarHOLFinite name value source).evaluateHOLFiniteState body with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      subst result
      have bound := bodyBound _ bodyFinal _ bodyResult (by simpa [setVarHOLFinite] using budget)
        (by simpa [setVarHOLFinite] using table) bodyRun nonerror bodyRel
      simp only [compileProgExactHOL]
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid,
        controlSteps_dec _ _ _ _ _ value targetEval valid, bound]
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror
private theorem boundWhile {g : PanGlobalsContextExact 64} {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop} {limit : Nat} {condition : ExpHOL 64} {body : ProgHOL 64}
    (bodyBound : Bound g P limit body) : Bound g P limit (.while condition body) := by
  classical
  intro σ source sourceFinal target result budget table run nonerror rel
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
        have bodyBudget : source.decClockHOLFinite.clock ≤ limit := by simp only [decClockHOLFinite]; omega
        have bodyTable : P source.decClockHOLFinite.code := table
        have bodyCost := bodyBound source.decClockHOLFinite sourcePost target.decClockHOLFinite bodyResult
          bodyBudget bodyTable bodyRun bodyNonerror bodyRel
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        have postBudget : sourcePost.clock ≤ limit := by omega
        have postCode : sourcePost.code = source.code := by
          have h := SemInitSupport.eval_code source.decClockHOLFinite body
          rw [bodyRun] at h
          simpa [decClockHOLFinite] using h
        have postTable : P sourcePost.code := by rw [postCode]; exact table
        simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩),bodyRun] at sourceCount
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result postBudget postTable (by simpa using run) nonerror postRel rfl
          simp only [compileProgExactHOL] at recurse
          simp only at sourceCount ⊢
          rw [bodyCost,recurse,← sourceCount]
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal targetPost result postBudget postTable (by simpa using run) nonerror postRel rfl
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

private theorem compiledArgs (g : PanGlobalsContextExact 64) (args : List (ExpHOL 64)) :
    compileExpExactHOLList g args = args.map (compileExpExactHOL g) := by
  induction args with
  | nil => simp [compileExpExactHOLList]
  | cons e es ih => simp [compileExpExactHOLList,ih]

/-- A tail call into a global-aware callee preserves its control-visit count. -/
private theorem tailReached {σ : Type} (globals : PanGlobalsContextExact 64)
    (function : MlS) (args : List (ExpHOL 64)) (callee : ProgHOL 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (values : List (ValueHOL 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (sourceArgs : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) args = some values)
    (sourceFound : lookupCodeHOLFinite source.code.lookup function values = some (callee,locals,returnShape))
    (clock : source.clock ≠ 0)
    (run : source.evaluateHOLFiniteState (.call none function args) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target)
    (calleeBound : ∀ (bodyResult : Option (PanSemResultExact 64)) (bodyFinal : PanSemStateFiniteExact 64 σ),
      (callEntryStateHOLFinite source locals).evaluateHOLFiniteState callee = (bodyResult,bodyFinal) →
      bodyResult ≠ some .error →
      panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) →
      controlSteps (compileProgExactHOL globals callee) (callEntryStateHOLFinite target locals) =
        controlSteps callee (callEntryStateHOLFinite source locals)) :
    controlSteps (compileProgExactHOL globals (.call none function args)) target =
      controlSteps (.call none function args) source := by
  have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL globals source target args values ⟨rel,sourceArgs⟩
  rw [← compiledArgs] at targetArgs
  have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL globals source target true
    function values callee locals returnShape ⟨rel,sourceFound⟩
  have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
  have targetClock : target.clock ≠ 0 := clockRel ▸ clock
  have decremented := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
  have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals source.decClockHOLFinite
    target.decClockHOLFinite true locals).1 decremented
  change panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) at entryRel
  rcases bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState callee with ⟨bodyResult,bodyFinal⟩
  have bodyNonerror : bodyResult ≠ some .error := by
    intro bad
    simp only [evaluateHOLFiniteState_call,sourceArgs,sourceFound,if_neg clock,bodyRun,bad] at run
    exact nonerror (Prod.mk.inj run).1.symm
  have equal := calleeBound bodyResult bodyFinal bodyRun bodyNonerror entryRel
  simp only [compileProgExactHOL]
  rw [controlSteps_tailCall _ _ source values callee locals returnShape sourceArgs sourceFound clock,
    controlSteps_tailCall _ _ target values (compileProgExactHOL globals callee) locals returnShape targetArgs targetFound targetClock,equal]


private theorem returningReached {σ : Type} (globals : PanGlobalsContextExact 64)
    (dest function : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) (callee cont : ProgHOL 64)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (values : List (ValueHOL 64)) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (value : ValueHOL 64) (bodyFinal : PanSemStateFiniteExact 64 σ)
    (sourceArgs : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) args = some values)
    (sourceFound : lookupCodeHOLFinite source.code.lookup function values = some (callee,locals,returnShape))
    (clock : source.clock ≠ 0)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState callee = (some (.returned value),bodyFinal))
    (valid : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (returnValid : shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (run : source.evaluateHOLFiniteState (.decCall dest shape function args cont) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : panGlobalsStateRelHOLExact true globals source target)
    (calleeBound : controlSteps (compileProgExactHOL globals callee) (callEntryStateHOLFinite target locals) =
      controlSteps callee (callEntryStateHOLFinite source locals))
    (contBound : ∀ sourceNext targetNext : PanSemStateFiniteExact 64 σ,
      sourceNext.code = source.code → sourceNext.clock < source.clock →
      panGlobalsStateRelHOLExact true globals sourceNext targetNext →
      (sourceNext.evaluateHOLFiniteState cont).1 ≠ some .error →
      controlSteps (compileProgExactHOL globals cont) targetNext = controlSteps cont sourceNext) :
    controlSteps (compileProgExactHOL globals (.decCall dest shape function args cont)) target =
      controlSteps (.decCall dest shape function args cont) source := by
  have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL globals source target args values ⟨rel,sourceArgs⟩
  rw [← compiledArgs] at targetArgs
  have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL globals source target true
    function values callee locals returnShape ⟨rel,sourceFound⟩
  have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
  have targetClock : target.clock ≠ 0 := clockRel ▸ clock
  have decremented := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
  have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals source.decClockHOLFinite
    target.decClockHOLFinite true locals).1 decremented
  change panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) at entryRel
  obtain ⟨targetBodyFinal,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL callee
    (callEntryStateHOLFinite source locals) (some (.returned value)) globals (callEntryStateHOLFinite target locals) bodyFinal
    ⟨entryRel,bodyRun,by simp⟩
  simp only [goodResHOL] at postRel
  have localsEq : source.locals = target.locals := rel.2.1 rfl
  have restored := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals bodyFinal targetBodyFinal true source.locals).2 postRel
  have nextRel := PanGlobalsStateRelationLocals.stateRelSetVarHOL globals {bodyFinal with locals := source.locals}
    {targetBodyFinal with locals := source.locals} true dest value restored
  have nextNonerror : ((setVarHOLFinite dest value {bodyFinal with locals := source.locals}).evaluateHOLFiniteState cont).1 ≠ some .error := by
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [sourceArgs,sourceFound,if_neg clock,bodyRun,valid,returnValid,Bool.true_and,if_true] at run
    exact fun bad => nonerror ((Prod.mk.inj run).1.symm.trans bad)
  have nextCode : (setVarHOLFinite dest value {bodyFinal with locals := source.locals}).code = source.code := by
    have h := SemInitSupport.eval_code (callEntryStateHOLFinite source locals) callee
    rw [bodyRun] at h
    simpa [setVarHOLFinite,callEntryStateHOLFinite] using h
  have nextClock : (setVarHOLFinite dest value {bodyFinal with locals := source.locals}).clock < source.clock := by
    have h := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source locals) callee
    rw [bodyRun] at h
    simp only [setVarHOLFinite,callEntryStateHOLFinite] at h ⊢
    omega
  have continuationCost := contBound _ _ nextCode nextClock nextRel nextNonerror
  have fixed : fixClockHOLFinite (callEntryStateHOLFinite source locals) (some (PanSemResultExact.returned value),bodyFinal) =
    (some (PanSemResultExact.returned value),bodyFinal) := by rw [← bodyRun,fixClockHOLFinite_evaluateState]
  have fixedTarget : fixClockHOLFinite (callEntryStateHOLFinite target locals) (some (PanSemResultExact.returned value),targetBodyFinal) =
    (some (PanSemResultExact.returned value),targetBodyFinal) := by rw [← targetRun,fixClockHOLFinite_evaluateState]
  simp only [compileProgExactHOL]
  rw [controlSteps_decCall_return _ _ _ _ _ source values callee locals returnShape value bodyFinal
    sourceArgs sourceFound clock bodyRun valid returnValid,
    controlSteps_decCall_return _ _ _ _ _ target values (compileProgExactHOL globals callee) locals returnShape value targetBodyFinal
    targetArgs targetFound targetClock targetRun valid returnValid]
  simp only [fixed,fixedTarget,localsEq]
  simp only [localsEq] at continuationCost
  rw [calleeBound,continuationCost]
/-- A terminal global-aware callee contributes no continuation visits. -/
private theorem terminalReached {σ : Type} (globals : PanGlobalsContextExact 64)
    (dest function : MlS) (shape : ShapeHOL) (args : List (ExpHOL 64)) (callee cont : ProgHOL 64)
    (source target : PanSemStateFiniteExact 64 σ) (values : List (ValueHOL 64))
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64)) (bodyFinal : PanSemStateFiniteExact 64 σ)
    (sourceArgs : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) args = some values)
    (sourceFound : lookupCodeHOLFinite source.code.lookup function values = some (callee,locals,returnShape))
    (clock : source.clock ≠ 0)
    (bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState callee = (result,bodyFinal))
    (nonerror : result ≠ some .error) (terminal : ∀ value, result ≠ some (.returned value))
    (rel : panGlobalsStateRelHOLExact true globals source target)
    (calleeBound : controlSteps (compileProgExactHOL globals callee) (callEntryStateHOLFinite target locals) =
      controlSteps callee (callEntryStateHOLFinite source locals)) :
    controlSteps (compileProgExactHOL globals (.decCall dest shape function args cont)) target =
      controlSteps (.decCall dest shape function args cont) source := by
  have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL globals source target args values ⟨rel,sourceArgs⟩
  rw [← compiledArgs] at targetArgs
  have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL globals source target true
    function values callee locals returnShape ⟨rel,sourceFound⟩
  have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
  have targetClock : target.clock ≠ 0 := clockRel ▸ clock
  have decremented := PanGlobalsStateRelationClock.stateRelDecClockHOL globals source target true rel
  have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL globals source.decClockHOLFinite
    target.decClockHOLFinite true locals).1 decremented
  change panGlobalsStateRelHOLExact true globals (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) at entryRel
  obtain ⟨targetBodyFinal,targetRun,_⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL callee
    (callEntryStateHOLFinite source locals) result globals (callEntryStateHOLFinite target locals) bodyFinal
    ⟨entryRel,bodyRun,nonerror⟩
  simp only [compileProgExactHOL]
  rw [controlSteps_decCall_terminal _ _ _ _ _ source values callee locals returnShape result bodyFinal
    sourceArgs sourceFound clock bodyRun terminal,
    controlSteps_decCall_terminal _ _ _ _ _ target values (compileProgExactHOL globals callee) locals returnShape result targetBodyFinal
    targetArgs targetFound targetClock targetRun terminal,calleeBound]
private theorem frontendBound {g : PanGlobalsContextExact 64}
    {P : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) → Prop}
    {ctxt : PanToCrepContextExact 64} {p : ProgHOL 64} (shape : GlobalFrontend g ctxt p)
    (limit : Nat) : Bound g P limit p := by
  induction shape with
  | skip | «break» | «continue» | tick | store | storeValue | assignLocal | ret =>
    intro σ source sourceFinal target result budget table run nonerror rel
    simp [compileProgExactHOL,controlSteps.eq_def]
  | assignGlobal found e =>
    intro σ source sourceFinal target result budget table run nonerror rel
    simp [compileProgExactHOL,found,controlSteps.eq_def]
  | assignGlobalStruct found e =>
    intro σ source sourceFinal target result budget table run nonerror rel
    simp [compileProgExactHOL,found,controlSteps.eq_def]
  | decl e body ih => exact boundDecl _ .one ih
  | declValue e positive body ih => exact boundDecl _ _ ih
  | seq a b iha ihb => exact boundSeq iha ihb
  | ite e a b iha ihb => exact boundIte iha ihb
  | «while» e body ih => exact boundWhile ih

/-- Global lowering preserves control visits for all call-free programs in
    the global frontend, including loops. -/
theorem globalFrontend_controlSteps {g : PanGlobalsContextExact 64} {ctxt : PanToCrepContextExact 64}
    {p : ProgHOL 64} (shape : GlobalFrontend g ctxt p)
    {σ : Type} (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true g source target) :
    controlSteps (compileProgExactHOL g p) target = controlSteps p source :=
  frontendBound (P := fun _ => True) shape source.clock source sourceFinal target result (Nat.le_refl _) trivial run nonerror rel

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
private theorem globalCallBound (g : PanGlobalsContextExact 64) (limit : Nat) :
    ∀ ctxt p, GlobalCallFrontend g ctxt p → Bound g (GlobalCallTable g) limit p := by
  induction limit using Nat.strongRecOn with
  | _ limit clockIH =>
    intro ctxt p supported
    induction supported with
    | base h => exact frontendBound h limit
    | @tail ctxt name args scalar =>
      intro σ source sourceFinal target result budget table run nonerror rel
      cases argsEval : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) args with
      | none =>
        simp only [evaluateHOLFiniteState_call,argsEval] at run
        exact absurd (Prod.mk.inj run).1.symm nonerror
      | some values =>
        cases found : lookupCodeHOLFinite source.code.lookup name values with
        | none =>
          simp only [evaluateHOLFiniteState_call,argsEval,found] at run
          exact absurd (Prod.mk.inj run).1.symm nonerror
        | some entry =>
          obtain ⟨callee,locals,rsh⟩ := entry
          by_cases noClock : source.clock = 0
          · have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL g source target args values ⟨rel,argsEval⟩
            rw [← compiledArgs] at targetArgs
            have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL g source target true name values callee locals rsh ⟨rel,found⟩
            have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
            have targetClock : target.clock = 0 := clockRel ▸ noClock
            simp only [compileProgExactHOL]
            rw [controlSteps.eq_def,controlSteps.eq_def (.call none _ _)]
            simp only [argsEval,targetArgs,found,targetFound,if_pos noClock,if_pos targetClock]
          · obtain ⟨calleeCtxt,calleeShape⟩ := table _ _ _ _ _ found
            apply tailReached g name args callee source sourceFinal target result values locals rsh argsEval found noClock run nonerror rel
            intro bodyResult bodyFinal bodyRun bodyNonerror entryRel
            have smaller : (callEntryStateHOLFinite source locals).clock < limit := by
              simp only [callEntryStateHOLFinite]
              omega
            have calleeControl : Bound g (GlobalCallTable g) (callEntryStateHOLFinite source locals).clock callee :=
              clockIH _ smaller calleeCtxt callee calleeShape
            exact calleeControl _ bodyFinal _ bodyResult (Nat.le_refl _) (by simpa [callEntryStateHOLFinite] using table)
              bodyRun bodyNonerror entryRel
    | @decCall ctxt dest shape name args cont scalar contShape contIH =>
      intro σ source sourceFinal target result budget table run nonerror rel
      cases argsEval : @evalListHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) args with
      | none =>
        simp only [evaluateHOLFiniteState_decCall_fixClockRewrite,argsEval] at run
        exact absurd (Prod.mk.inj run).1.symm nonerror
      | some values =>
        cases found : lookupCodeHOLFinite source.code.lookup name values with
        | none =>
          simp only [evaluateHOLFiniteState_decCall_fixClockRewrite,argsEval,found] at run
          exact absurd (Prod.mk.inj run).1.symm nonerror
        | some entry =>
          obtain ⟨callee,locals,rsh⟩ := entry
          by_cases noClock : source.clock = 0
          · have targetArgs := PanGlobalsOptMmapEvalCorrect.optMmapEvalCorrectHOL g source target args values ⟨rel,argsEval⟩
            rw [← compiledArgs] at targetArgs
            have targetFound := PanGlobalsStateRelationCode.stateRelLookupCodeHOL g source target true name values callee locals rsh ⟨rel,found⟩
            have clockRel : source.clock = target.clock := rel.2.2.2.2.2.1
            have targetClock : target.clock = 0 := clockRel ▸ noClock
            simp only [compileProgExactHOL]
            rw [controlSteps.eq_def,controlSteps.eq_def (.decCall _ _ _ _ _)]
            simp only [argsEval,targetArgs,found,targetFound,if_pos noClock,if_pos targetClock]
          · obtain ⟨calleeCtxt,calleeShape⟩ := table _ _ _ _ _ found
            have decremented := PanGlobalsStateRelationClock.stateRelDecClockHOL g source target true rel
            have entryRel := (PanGlobalsStateRelationLocals.stateRelChangeLocalsHOL g source.decClockHOLFinite
              target.decClockHOLFinite true locals).1 decremented
            change panGlobalsStateRelHOLExact true g (callEntryStateHOLFinite source locals) (callEntryStateHOLFinite target locals) at entryRel
            rcases bodyRun : (callEntryStateHOLFinite source locals).evaluateHOLFiniteState callee with ⟨bodyResult,bodyFinal⟩
            have bodyNonerror : bodyResult ≠ some .error := by
              intro bad
              simp only [evaluateHOLFiniteState_decCall_fixClockRewrite,argsEval,found,if_neg noClock,bodyRun,bad] at run
              exact nonerror (Prod.mk.inj run).1.symm
            have smaller : (callEntryStateHOLFinite source locals).clock < limit := by
              simp only [callEntryStateHOLFinite]
              omega
            have calleeControl : Bound g (GlobalCallTable g) (callEntryStateHOLFinite source locals).clock callee :=
              clockIH _ smaller calleeCtxt callee calleeShape
            have calleeBound := calleeControl _ bodyFinal _ bodyResult (Nat.le_refl _)
              (by simpa [callEntryStateHOLFinite] using table) bodyRun bodyNonerror entryRel
            by_cases returned : ∃ value, bodyResult = some (.returned value)
            · obtain ⟨value,rfl⟩ := returned
              have valid : shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) rsh = true := by
                by_contra invalid
                have bad : (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) rsh) = false := by
                  cases h₁ : shapeEqHOL (shapeOfHOLExact value) shape <;>
                    cases h₂ : shapeEqHOL (shapeOfHOLExact value) rsh <;> simp_all
                simp only [evaluateHOLFiniteState_decCall_fixClockRewrite,argsEval,found,if_neg noClock,bodyRun,bad,Bool.false_eq_true,if_false] at run
                exact nonerror (Prod.mk.inj run).1.symm
              apply returningReached g dest name shape args callee cont source sourceFinal target result values locals rsh value bodyFinal
                argsEval found noClock bodyRun valid.1 valid.2 run nonerror rel calleeBound
              intro sourceNext targetNext nextCode nextClock nextRel nextNonerror
              have nextBudget : sourceNext.clock ≤ limit := by omega
              have nextTable : GlobalCallTable g sourceNext.code := by rw [nextCode]; exact table
              rcases nextRun : sourceNext.evaluateHOLFiniteState cont with ⟨nextResult,nextFinal⟩
              exact contIH sourceNext nextFinal targetNext nextResult nextBudget nextTable nextRun
                (by simpa [nextRun] using nextNonerror) nextRel
            · have terminal : ∀ value, bodyResult ≠ some (.returned value) := by
                intro value h; exact returned ⟨value,h⟩
              exact terminalReached g dest name shape args callee cont source target values locals rsh bodyResult bodyFinal
                argsEval found noClock bodyRun bodyNonerror terminal rel calleeBound
    | decl e body ih => exact boundDecl _ .one ih
    | seq a b iha ihb => exact boundSeq iha ihb
    | ite e a b iha ihb => exact boundIte iha ihb
    | «while» e body ih => exact boundWhile ih
/-- Global lowering preserves visits for call-aware programs, including
    nested calls, recursion and loops. -/
theorem globalCallFrontend_controlSteps {g : PanGlobalsContextExact 64} {ctxt : PanToCrepContextExact 64}
    {p : ProgHOL 64} (shape : GlobalCallFrontend g ctxt p)
    {σ : Type} (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (table : GlobalCallTable g source.code)
    (run : source.evaluateHOLFiniteState p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (rel : panGlobalsStateRelHOLExact true g source target) :
    controlSteps (compileProgExactHOL g p) target = controlSteps p source :=
  globalCallBound g source.clock ctxt p shape source sourceFinal target result (Nat.le_refl _) table run nonerror rel

/-- Global-aware calls and loops reach Crep with an explicit bound depending
    on the generated entry, compiled code table, and source visit budget. -/
theorem globalCallFrontend_correct_with_steps {σ : Type}
    (globals : PanGlobalsContextExact 64) (ctxt : PanToCrepContextExact 64) (p : ProgHOL 64)
    (shape : GlobalCallFrontend globals ctxt p)
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (crep : CrepSemHOLState 64 σ) (programs : List (MlS × List Nat × CrepProgHOL 64)) (sourceLimit : Nat)
    (sourceTable : GlobalCallTable globals source.code)
    (compiledTable : crep.code = alistToFmapCodeExact programs) (targetTable : CallFrontendCode ctxt target.code)
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
        max (SteppedFlapjack.CrepSteps.statementWeight (compileProgExactHOLW ctxt (compileProgExactHOL globals p)))
          (SteppedFlapjack.CrepSteps.codeWeight programs) * sourceLimit := by
  obtain ⟨targetFinal,targetRun,globalFinal⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    p source result globals target sourceFinal ⟨globalRel,run,nonerror⟩
  have hshape := globalCallFrontend_compiled shape
  have visitEq := globalCallFrontend_controlSteps shape source sourceFinal target result sourceTable run nonerror globalRel
  have bound := callFrontend_compiled_steps ctxt (compileProgExactHOL globals p) hshape target targetFinal result crep
    programs compiledTable targetTable targetRun nonerror stateRel codeRel excpRel localsRel
  have correct : pcCompileCorrectAt (compileProgExactHOL globals p) target :=
    (pcCompileCorrectAt_iff_HOL _ _).mpr (pcCompileCorrect_all _ _)
  obtain ⟨crepResult,crepFinal,crepRun,finalRel,_,_,resultRel⟩ :=
    correct result targetFinal crep ctxt targetRun nonerror stateRel codeRel excpRel localsRel (callFrontend_localised hshape)
  refine ⟨targetFinal,crepResult,crepFinal,targetRun,globalFinal,crepRun,finalRel,resultRel,?_⟩
  rw [visitEq] at bound
  exact bound.trans (Nat.mul_le_mul_left _ sourceBound)
end SteppedFlapjack.PanToCrepSteps
