import SteppedFlapjack.Concrete.ScalarParity
/-! Source lexical-scope preservation for supported control flow. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def ScalarScopeResult {σ : Type} (scope : List VarName) : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop
  | none, final => ScalarScopePresent scope final
  | some .break, _ | some .continue, _ => False
  | _, _ => True

private def ScopeBridge (scope : List VarName) (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ {σ : Type} (source final : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64)),
    ScalarScopePresent scope source → source.evaluateHOLFiniteState (progToHOL program) = (result,final) →
      ScalarScopeResult scope result final

private theorem scopeSkip {scope : List VarName} : ScopeBridge scope .skip := by
  intro σ source final result present run
  simp only [progToHOL,evaluateHOLFiniteState_skip,Prod.mk.injEq] at run
  obtain ⟨rfl,rfl⟩ := run
  exact present

private theorem scopeReturn {scope : List VarName} {expression : Exp (RiscV.Word 64)} : ScopeBridge scope (.return expression) := by
  intro σ source final result present run
  simp only [progToHOL,evaluateHOLFiniteState_return] at run
  split at run
  · simp only [Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    trivial
  · split at run <;> simp only [Prod.mk.injEq] at run <;> obtain ⟨rfl,rfl⟩ := run <;> trivial

private theorem scopeAssign {scope : List VarName} (name : VarName) {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) : ScopeBridge scope (.assign .local name expression) := by
  intro σ source final result present run
  simp only [progToHOL,evaluateHOLFiniteState_assign] at run
  cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) with
  | none =>
    simp only [evaluated,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    trivial
  | some value =>
    obtain ⟨word,rfl⟩ := scalar_hol_word scalar source present value evaluated
    simp only [evaluated] at run
    split at run
    · simp only [Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      intro item member
      exact (present.setVar name word) item (by simp [member])
    · simp only [Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      trivial
private theorem scopeSeq {scope : List VarName} {a b : Prog (RiscV.Word 64)}
    (aScope : ScopeBridge scope a) (bScope : ScopeBridge scope b) : ScopeBridge scope (.seq a b) := by
  intro σ source final result present run
  simp only [progToHOL,evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : source.evaluateHOLFiniteState (progToHOL a) with
  | mk firstResult middle =>
    rw [firstRun] at run
    have firstScope := aScope source middle firstResult present firstRun
    cases firstResult with
    | none =>
      exact bScope middle final result firstScope run
    | some first =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      exact firstScope

private theorem scopeIte {scope : List VarName} {condition : Exp (RiscV.Word 64)} {a b : Prog (RiscV.Word 64)}
    (aScope : ScopeBridge scope a) (bScope : ScopeBridge scope b) : ScopeBridge scope (.ite condition a b) := by
  intro σ source final result present run
  simp only [progToHOL,evaluateHOLFiniteState_ite] at run
  split at run
  case h_2 =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    trivial
  rename_i word evaluated
  by_cases zero : word = 0
  · simp only [zero] at run
    exact bScope source final result present run
  · simp only [if_neg zero] at run
    exact aScope source final result present run

private theorem scopeDecl {scope : List VarName} (name : VarName) {initializer : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (scalar : Scalar scope initializer) (bodyScope : ScopeBridge (name :: scope) body) : ScopeBridge scope (.dec name .one initializer body) := by
  intro σ source final result present run
  simp only [progToHOL,shapeToHOL,evaluateHOLFiniteState_dec_total] at run
  cases evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL initializer) with
  | none =>
    simp only [evaluated,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    trivial
  | some value =>
    obtain ⟨word,rfl⟩ := scalar_hol_word scalar source present value evaluated
    have valid : shapeEqHOL .one (shapeOfHOLExact (.val (.word word))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
    simp only [evaluated,valid,if_true] at run
    rcases bodyRun : (setVarHOLFinite (ofString name) (.val (.word word)) source).evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,bodyFinal⟩
    rw [bodyRun] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    have bodyPresent := present.setVar name word
    have outcome := bodyScope _ bodyFinal bodyResult bodyPresent bodyRun
    cases bodyResult with
    | none => exact ScalarScopePresent.restore source bodyFinal name present outcome
    | some r =>
      cases r <;> simp_all [ScalarScopeResult]

private theorem scopeWhile {scope : List VarName} {condition : Exp (RiscV.Word 64)} {body : Prog (RiscV.Word 64)}
    (bodyScope : ScopeBridge scope body) : ScopeBridge scope (.while condition body) := by
  intro σ source final result present run
  simp only [progToHOL] at run
  induction hc : source.clock using Nat.strongRecOn generalizing source final result with
  | _ clock ih =>
    rw [evaluateHOLFiniteState_while_fixClockRewrite] at run
    split at run
    case h_2 =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      trivial
    rename_i word evaluated
    by_cases zero : word = 0
    · simp [zero] at run
      obtain ⟨rfl,rfl⟩ := run
      exact present
    · have zeroBits : word ≠ (0#64) := by simpa using zero
      by_cases noClock : source.clock = 0
      · simp [zeroBits,noClock] at run
        obtain ⟨rfl,rfl⟩ := run
        trivial
      · simp only [if_pos zero,if_neg noClock] at run
        rcases bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState (progToHOL body) with ⟨bodyResult,bodyFinal⟩
        rw [bodyRun] at run
        simp only at run
        have entryPresent : ScalarScopePresent scope source.decClockHOLFinite := by simpa [ScalarScopePresent,decClockHOLFinite] using present
        have bodyResultScope := bodyScope source.decClockHOLFinite bodyFinal bodyResult entryPresent bodyRun
        have clockLe := evaluateHOLFiniteState_clock_le source.decClockHOLFinite (progToHOL body)
        rw [bodyRun] at clockLe
        have smaller : bodyFinal.clock < clock := by simp only [decClockHOLFinite] at clockLe; omega
        cases bodyResult with
        | none =>
          exact ih bodyFinal.clock smaller bodyFinal final result bodyResultScope (by simpa using run) rfl
        | some r =>
          cases r with
          | «break» | «continue» => exact False.elim bodyResultScope
          | error | timeOut | returned _ | finalFfi _ | exception _ _ =>
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
            trivial

private theorem supportedScopeBridge {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ScopeBridge scope program := by
  induction supported with
  | skip => exact scopeSkip
  | assign name member scalar => exact scopeAssign name scalar
  | decl name scalar body ih => exact scopeDecl name scalar ih
  | seq a b iha ihb => exact scopeSeq iha ihb
  | ite scalar a b iha ihb => exact scopeIte iha ihb
  | «while» scalar body ih => exact scopeWhile ih
  | ret scalar => exact scopeReturn

/-- Normal execution preserves each in-scope scalar local; supported programs
never produce a top-level break or continue. -/
theorem supported_scope_result {σ : Type} {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (source final : PanSemStateFiniteExact 64 σ)
    (result : Option (PanSemResultExact 64)) (present : ScalarScopePresent scope source)
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,final)) :
    ScalarScopeResult scope result final :=
  supportedScopeBridge supported source final result present run

end SteppedFlapjack.Concrete
