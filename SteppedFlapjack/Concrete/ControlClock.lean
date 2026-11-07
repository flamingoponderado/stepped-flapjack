import SteppedFlapjack.Concrete.FrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps Flapjack.Basis.Pure.MlString

def programWeight : Prog (RiscV.Word 64) → Nat
  | .dec _ _ _ body => 1 + programWeight body
  | .seq a b => 1 + programWeight a + programWeight b
  | .ite _ a b => 1 + programWeight a + programWeight b
  | .while _ body => 1 + programWeight body
  | _ => 1

private def ClockBound (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal) → result ≠ some .error →
    controlSteps (progToHOL program) source ≤ programWeight program * (source.clock - sourceFinal.clock + 1)

private theorem weightPos (program : Prog (RiscV.Word 64)) : 1 ≤ programWeight program := by
  cases program <;> simp [programWeight] <;> omega

private theorem clockSeq {a b : Prog (RiscV.Word 64)} (aBound : ClockBound a) (bBound : ClockBound b) :
    ClockBound (.seq a b) := by
  intro σ source sourceFinal result run nonerror
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_seq_line780] at run
  rcases firstRun : source.evaluateHOLFiniteState (progToHOL a) with ⟨firstResult,middle⟩
  rw [firstRun] at run
  dsimp only at run
  have firstNonerror : firstResult ≠ some .error := by
    intro h
    rw [h] at run
    exact nonerror (Prod.mk.inj run).1.symm
  have firstCost := aBound source middle firstResult firstRun firstNonerror
  have firstClock := evaluateHOLFiniteState_clock_le source (progToHOL a)
  rw [firstRun] at firstClock
  rw [controlSteps_seq,firstRun]
  cases firstResult with
  | none =>
    have secondCost := bBound middle sourceFinal result run nonerror
    have secondClock := evaluateHOLFiniteState_clock_le middle (progToHOL b)
    have secondRun : middle.evaluateHOLFiniteState (progToHOL b) = (result,sourceFinal) := by simpa using run
    rw [secondRun] at secondClock
    simp only [programWeight]
    have pa := weightPos a
    have pb := weightPos b
    simp only at firstClock secondClock ⊢
    have delta : source.clock - sourceFinal.clock = (source.clock-middle.clock) + (middle.clock-sourceFinal.clock) := by omega
    rw [delta]
    nlinarith
  | some r =>
    obtain ⟨_,rfl⟩ := Prod.mk.inj run
    simp only [programWeight]
    have pb := weightPos b
    simp only at firstClock ⊢
    nlinarith

private theorem clockIte {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (aBound : ClockBound a) (bBound : ClockBound b) : ClockBound (.ite condition a b) := by
  classical
  intro σ source sourceFinal result run nonerror
  simp only [progToHOL] at run ⊢
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
  rename_i w heval
  rw [controlSteps_ite]
  simp only [heval,programWeight]
  have pa := weightPos a
  have pb := weightPos b
  by_cases zero : w = 0
  · simp only [zero] at run
    simp only [zero,ne_eq,not_true_eq_false,if_false]
    have cost := bBound source sourceFinal result run nonerror
    nlinarith
  · simp only [if_neg zero] at run
    simp only [if_pos zero]
    have cost := aBound source sourceFinal result run nonerror
    nlinarith

private theorem clockDecl (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (bodyBound : ClockBound body) : ClockBound (.dec name .one initializer body) := by
  classical
  intro σ source sourceFinal result run nonerror
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
      rcases bodyRun : (setVarHOLFinite (ofString name) value source).evaluateHOLFiniteState
          (progToHOL body) with ⟨bodyResult,bodyFinal⟩
      rw [bodyRun] at run
      have sameResult : bodyResult = result := (Prod.mk.inj run).1
      have sameClock : bodyFinal.clock = sourceFinal.clock := by
        have h := congrArg (fun s : PanSemStateFiniteExact 64 σ => s.clock) (Prod.mk.inj run).2
        simpa using h
      subst result
      have bound := bodyBound (setVarHOLFinite (ofString name) value source) bodyFinal bodyResult bodyRun nonerror
      rw [controlSteps_dec _ _ _ _ _ value evaluated valid]
      simp only [programWeight,setVarHOLFinite] at bound ⊢
      rw [← sameClock]
      nlinarith
    · simp only [valid,Bool.false_eq_true,ite_false] at run
      exact absurd (Prod.mk.inj run).1.symm nonerror

private theorem clockWhile {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (bodyBound : ClockBound body) : ClockBound (.while condition body) := by
  classical
  intro σ source sourceFinal result run nonerror
  simp only [progToHOL] at run ⊢
  induction hc : source.clock using Nat.strongRecOn generalizing source sourceFinal result with
  | _ clock ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 => exact absurd (Prod.mk.inj run).1.symm nonerror
    rename_i w heval
    have hevalExact : @evalHOLExact 64 σ _ source.toExact
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) = some (.val (.word w)) := heval
    rw [controlSteps_while]
    simp only [hevalExact,programWeight]
    rw [← hc]
    by_cases nz : w ≠ 0
    · by_cases z : source.clock = 0
      · simp only [if_pos nz,if_pos z] at run
        obtain ⟨_,rfl⟩ := Prod.mk.inj run
        simp only [z,ne_eq,not_true_eq_false,and_false,if_false,Nat.add_zero,emptyLocalsHOLFinite]
        have p := weightPos body
        omega
      · simp only [if_pos (show w ≠ 0 ∧ source.clock ≠ 0 from ⟨nz,z⟩)]
        rw [if_pos nz,if_neg z] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,sourcePost⟩
        rw [bodyRun] at run
        dsimp only at run
        have bodyNonerror : bodyResult ≠ some .error := by
          rintro rfl
          exact absurd (Prod.mk.inj run).1.symm nonerror
        have bodyCost := bodyBound source.decClockHOLFinite sourcePost bodyResult bodyRun bodyNonerror
        have bodyClock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at bodyClock
        have smaller : sourcePost.clock < clock := by
          simp only [decClockHOLFinite] at bodyClock
          omega
        cases bodyResult with
        | none =>
          have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result nonerror (by simpa using run) rfl
          have finalClock := evaluateHOLFiniteState_clock_le sourcePost (.while (expToHOL condition) (progToHOL body))
          have restRun : sourcePost.evaluateHOLFiniteState (.while (expToHOL condition) (progToHOL body)) = (result,sourceFinal) := by simpa using run
          rw [restRun] at finalClock
          change controlSteps (progToHOL body) source.decClockHOLFinite ≤
            programWeight body * (source.clock-1-sourcePost.clock+1) at bodyCost
          simp only [programWeight] at recurse
          simp only at bodyClock finalClock ⊢
          have delta : source.clock-sourceFinal.clock = 1+(source.clock-1-sourcePost.clock)+(sourcePost.clock-sourceFinal.clock) := by omega
          rw [delta]
          nlinarith
        | some r =>
          cases r with
          | «continue» =>
            have recurse := ih sourcePost.clock smaller sourcePost sourceFinal result nonerror (by simpa using run) rfl
            have finalClock := evaluateHOLFiniteState_clock_le sourcePost (.while (expToHOL condition) (progToHOL body))
            have restRun : sourcePost.evaluateHOLFiniteState (.while (expToHOL condition) (progToHOL body)) = (result,sourceFinal) := by simpa using run
            rw [restRun] at finalClock
            change controlSteps (progToHOL body) source.decClockHOLFinite ≤
              programWeight body * (source.clock-1-sourcePost.clock+1) at bodyCost
            simp only [programWeight] at recurse
            simp only at bodyClock finalClock ⊢
            have delta : source.clock-sourceFinal.clock = 1+(source.clock-1-sourcePost.clock)+(sourcePost.clock-sourceFinal.clock) := by omega
            rw [delta]
            nlinarith
          | error => exact absurd rfl bodyNonerror
          | «break» | timeOut | returned _ | finalFfi _ | exception _ _ =>
            have finalEq : sourcePost = sourceFinal := (Prod.mk.inj run).2
            subst sourceFinal
            change controlSteps (progToHOL body) source.decClockHOLFinite ≤
              programWeight body * (source.clock-1-sourcePost.clock+1) at bodyCost
            simp only [Nat.add_zero]
            simp only at bodyClock
            have delta : source.clock-sourcePost.clock = 1+(source.clock-1-sourcePost.clock) := by omega
            rw [delta]
            nlinarith
    · simp only [if_neg nz] at run
      obtain ⟨_,rfl⟩ := Prod.mk.inj run
      simp only [if_neg (show ¬ (w ≠ 0 ∧ source.clock ≠ 0) from fun h => nz h.1),Nat.add_zero,Nat.sub_self]
      have p := weightPos body
      omega

private theorem supportedClockBound {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ClockBound program := by
  induction supported with
  | skip | assign | ret =>
    intro σ source sourceFinal result run nonerror
    simp [progToHOL,controlSteps.eq_def,programWeight]
  | decl name scalar body ih => exact clockDecl name ih
  | seq a b iha ihb => exact clockSeq iha ihb
  | ite scalar a b iha ihb => exact clockIte iha ihb
  | «while» scalar body ih => exact clockWhile ih

/-- Supported source visits are bounded by program weight times consumed
clock plus one; the bound is valid for arbitrary nested loops. -/
theorem supported_control_clock {σ : Type} {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) (nonerror : result ≠ some .error) :
    controlSteps (progToHOL program) source ≤ programWeight program * (source.clock - sourceFinal.clock + 1) :=
  supportedClockBound supported.1 source sourceFinal result run nonerror

end SteppedFlapjack.Concrete
