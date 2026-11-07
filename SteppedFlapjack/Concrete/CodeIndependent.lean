import SteppedFlapjack.Concrete.FrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

theorem scalar_eval_code_irrel {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    @evalHOLExact 64 σ _ ({source with code := code} : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) =
    @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) := by
  induction scalar <;> simp_all [expToHOL,evalHOLExact,evalListHOLExact]
private def CodeIndependent (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source : PanSemStateFiniteExact 64 σ)
      (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)),
    ({source with code := code} : PanSemStateFiniteExact 64 σ).evaluateHOLFiniteState (progToHOL program) =
      let result := source.evaluateHOLFiniteState (progToHOL program)
      (result.1,{result.2 with code := code})

private theorem skipCode : CodeIndependent .skip := by
  intro σ source code
  simp [progToHOL,evaluateHOLFiniteState_skip]

private theorem returnCode {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) : CodeIndependent (.return expression) := by
  intro σ source code
  simp only [progToHOL,evaluateHOLFiniteState_return]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) with
  | none => simp
  | some value =>
    by_cases small : sizeOfShapeWithContextHOL source.structs (shapeOfHOLExact value) ≤ 32 <;>
      simp [small,emptyLocalsHOLFinite]

private theorem assignCode {scope : List VarName} (name : VarName) {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) : CodeIndependent (.assign .local name expression) := by
  intro σ source code
  simp only [progToHOL,evaluateHOLFiniteState_assign]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) with
  | none => simp
  | some value =>
    cases found : source.locals.lookup (ofString name) with
    | none => simp [isValidValueHOLExact,lookupKvarHOLExact,found]
    | some old =>
      by_cases valid : shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact old) = true <;>
        simp [isValidValueHOLExact,lookupKvarHOLExact,setKvarHOLFinite,setVarHOLFinite,found,valid]

private theorem seqCode {a b : Prog (RiscV.Word 64)} (aCode : CodeIndependent a) (bCode : CodeIndependent b) :
    CodeIndependent (.seq a b) := by
  intro σ source code
  simp only [progToHOL,evaluateHOLFiniteState_seq_line780]
  rcases firstRun : source.evaluateHOLFiniteState (progToHOL a) with ⟨firstResult,middle⟩
  have firstTarget := aCode source code
  rw [firstRun] at firstTarget
  simp only at firstTarget
  rw [firstTarget]
  cases firstResult with
  | none =>
    have secondTarget := bCode middle code
    exact secondTarget
  | some result => rfl

private theorem iteCode {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (aCode : CodeIndependent a) (bCode : CodeIndependent b) : CodeIndependent (.ite condition a b) := by
  intro σ source code
  simp only [progToHOL,evaluateHOLFiniteState_ite]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
  | none => rfl
  | some value =>
    cases value with
    | val w =>
      cases w with
      | word n =>
        by_cases zero : n = 0
        · simpa [zero] using bCode source code
        · have zeroBits : n ≠ (0#64) := by simpa using zero
          simpa [zeroBits] using aCode source code
    | rStruct _ => rfl
    | nStruct _ _ => rfl

private theorem declCode {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyCode : CodeIndependent body) : CodeIndependent (.dec name .one initializer body) := by
  intro σ source code
  simp only [progToHOL,shapeToHOL,evaluateHOLFiniteState_dec_total]
  rw [scalar_eval_code_irrel scalar source code]
  cases h : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
  | none => rfl
  | some value =>
    by_cases valid : shapeEqHOL .one (shapeOfHOLExact value) = true
    · simp only [valid,if_true]
      rcases bodyRun : (setVarHOLFinite (ofString name) value source).evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,bodyFinal⟩
      have bodyEq := bodyCode (setVarHOLFinite (ofString name) value source) code
      rw [bodyRun] at bodyEq
      simp only at bodyEq
      have codeRun : (setVarHOLFinite (ofString name) value {source with code := code}).evaluateHOLFiniteState (progToHOL body) =
          (bodyResult,{bodyFinal with code := code}) := by simpa [setVarHOLFinite] using bodyEq
      rw [codeRun]
    · simp [valid]
private theorem whileCode {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope condition) (bodyCode : CodeIndependent body) : CodeIndependent (.while condition body) := by
  intro σ source code
  induction hc : source.clock using Nat.strongRecOn generalizing source with
  | _ clock ih =>
    rw [← hc]
    simp only [progToHOL]
    rw [evaluateHOLFiniteState_while_fixClockRewrite,evaluateHOLFiniteState_while_fixClockRewrite]
    have evalEq : @evalHOLFinite 64 σ _ ({source with code := code} : PanSemStateFiniteExact 64 σ)
        (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) =
      @evalHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) :=
        scalar_eval_code_irrel scalar source code
    rw [evalEq]
    cases h : @evalHOLFinite 64 σ _ source (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL condition) with
    | none => rfl
    | some value =>
      cases value with
      | rStruct _ => rfl
      | nStruct _ _ => rfl
      | val word =>
        cases word with
        | word n =>
          by_cases zero : n = 0
          · simp [zero]
          · have zeroBits : n ≠ (0#64) := by simpa using zero
            by_cases noClock : source.clock = 0
            · simp [zeroBits,noClock,emptyLocalsHOLFinite]
            · simp only [if_neg noClock]
              simp only [if_pos zero]
              rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,post⟩
              have bodyEq := bodyCode source.decClockHOLFinite code
              rw [bodyRun] at bodyEq
              simp only at bodyEq
              have codeRun : ({source with code := code} : PanSemStateFiniteExact 64 σ).decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) =
                  (bodyResult,{post with code := code}) := by simpa [decClockHOLFinite] using bodyEq
              rw [codeRun]
              have monotone := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
              rw [bodyRun] at monotone
              have smaller : post.clock < clock := by
                simp only [decClockHOLFinite] at monotone
                omega
              have recursive := ih post.clock smaller post rfl
              simp only [progToHOL] at recursive
              cases bodyResult with
              | none => exact recursive
              | some result =>
                cases result with
                | «continue» => exact recursive
                | «break» | error | timeOut | returned _ | finalFfi _ | exception _ _ => rfl

private theorem supportedCode {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : CodeIndependent program := by
  induction supported with
  | skip => exact skipCode
  | assign name member scalar => exact assignCode name scalar
  | decl name scalar body ih => exact declCode name scalar ih
  | seq a b iha ihb => exact seqCode iha ihb
  | ite scalar a b iha ihb => exact iteCode scalar iha ihb
  | «while» scalar body ih => exact whileCode scalar ih
  | ret scalar => exact returnCode scalar

/-- Supported bodies do not inspect or change the code table, even on error. -/
theorem supported_code_irrel {σ : Type} {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    ({source with code := code} : PanSemStateFiniteExact 64 σ).evaluateHOLFiniteState (progToHOL program) =
      let result := source.evaluateHOLFiniteState (progToHOL program)
      (result.1,{result.2 with code := code}) :=
  supportedCode supported.1 source code

end SteppedFlapjack.Concrete
