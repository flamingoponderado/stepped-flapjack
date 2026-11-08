import SteppedFlapjack.Concrete.CodeIndependent
import SteppedFlapjack.PanToCrepSteps.ControlSteps
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps
private def ControlCode (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source : PanSemStateFiniteExact 64 σ)
      (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source

private theorem controlSkip : ControlCode .skip := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlReturn {expression : Exp (RiscV.Word 64)} : ControlCode (.return expression) := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlAssign (name : VarName) {expression : Exp (RiscV.Word 64)} : ControlCode (.assign .local name expression) := by
  intro σ source code
  simp [progToHOL,controlSteps.eq_def]

private theorem controlSeq {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (aSupported : SupportedIn scope a) (aCode : ControlCode a) (bCode : ControlCode b) : ControlCode (.seq a b) := by
  intro σ source code
  simp only [progToHOL,controlSteps_seq]
  have runEq := supportedIn_code_irrel aSupported source code
  rcases run : source.evaluateHOLFiniteState (progToHOL a) with ⟨result,post⟩
  rw [run] at runEq
  simp only at runEq
  rw [runEq,aCode]
  cases result with
  | none => simpa using bCode post code
  | some _ => rfl

private theorem controlIte {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (aCode : ControlCode a) (bCode : ControlCode b) : ControlCode (.ite condition a b) := by
  intro σ source code
  simp only [progToHOL,controlSteps_ite]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
  | none => rfl
  | some value =>
    cases value with
    | rStruct _ | nStruct _ _ => rfl
    | val word =>
      cases word with
      | word n =>
        by_cases zero : n = 0
        · simpa [zero] using bCode source code
        · have zeroBits : n ≠ (0#64) := by simpa using zero
          simpa [zeroBits] using aCode source code

private theorem controlDecl {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyCode : ControlCode body) : ControlCode (.dec name .one initializer body) := by
  intro σ source code
  simp only [progToHOL,shapeToHOL]
  have evalEq := scalar_eval_code_irrel scalar source code
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
  | none =>
    rw [controlSteps.eq_def,controlSteps.eq_def]
    simp only
    rw [evalEq,h]
  | some value =>
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · rw [controlSteps_dec _ _ _ _ _ value (evalEq.trans h) valid,controlSteps_dec _ _ _ _ _ value h valid]
      simpa [setVarHOLFinite] using bodyCode (setVarHOLFinite (ofString name) value source) code
    · rw [controlSteps.eq_def,controlSteps.eq_def]
      simp only
      rw [evalEq,h]
      simp [valid]

private theorem controlWhile {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (bodySupported : SupportedIn scope body) (bodyCode : ControlCode body) : ControlCode (.while condition body) := by
  intro σ source code
  induction hc : source.clock using Nat.strongRecOn generalizing source with
  | _ clock ih =>
    rw [← hc]
    simp only [progToHOL]
    rw [controlSteps_while,controlSteps_while]
    have evalEq := scalar_eval_code_irrel scalar source code
    rw [evalEq]
    cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
    | none => rfl
    | some value =>
      cases value with
      | rStruct _ | nStruct _ _ => rfl
      | val word =>
        cases word with
        | word n =>
          by_cases active : n ≠ 0 ∧ source.clock ≠ 0
          · simp only [if_pos active]
            rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨result,post⟩
            have bodyRunCode := supportedIn_code_irrel bodySupported source.decClockHOLFinite code
            rw [bodyRun] at bodyRunCode
            simp only at bodyRunCode
            have bodyRunCode' : ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) =
                (result,{post with code := code}) := by simpa [decClockHOLFinite] using bodyRunCode
            rw [bodyRunCode']
            have child : controlSteps (progToHOL body) ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite =
                controlSteps (progToHOL body) source.decClockHOLFinite := by simpa [decClockHOLFinite] using bodyCode source.decClockHOLFinite code
            rw [child]
            have mono := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
            rw [bodyRun] at mono
            have smaller : post.clock < clock := by simp [decClockHOLFinite] at mono; omega
            have recursive := ih post.clock smaller post rfl
            simp only [progToHOL] at recursive
            cases result with
            | none => simp [recursive]
            | some r => cases r <;> simp [recursive]
          · simp only [if_neg active]

private theorem supportedControlCode {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ControlCode program := by
  induction supported with
  | skip => exact controlSkip
  | assign name member scalar => exact controlAssign name
  | decl name scalar body ih => exact controlDecl name scalar ih
  | seq a b iha ihb => exact controlSeq a iha ihb
  | ite scalar a b iha ihb => exact controlIte scalar iha ihb
  | «while» scalar body ih => exact controlWhile scalar body ih
  | ret scalar => exact controlReturn

theorem supported_control_code_irrel {σ : Type} {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    controlSteps (progToHOL program) {source with code := code} = controlSteps (progToHOL program) source :=
  supportedControlCode supported.1 source code
end SteppedFlapjack.Concrete
