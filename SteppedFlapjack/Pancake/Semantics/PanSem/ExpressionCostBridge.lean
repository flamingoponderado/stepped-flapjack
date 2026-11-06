import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge

/-! Preserve expression costs at the executable-to-HOL boundary. -/
namespace Flapjack
open Flapjack.Pancake.PanLang

/-- The exact HOL expression's executable decoding supplies the same value and
its actual counted expression-node cost. No statement-step correspondence is
assumed here. -/
theorem evalPanValueExpCounted_decodeWithKeys_value_and_cost {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys)
    (expression : ExpHOL 64) (value : ValueHOL 64)
    (evaluated : exact.evalHOLFinite expression = some value) :
    let state := panSemExecStateOfHOLWithKeys exact ffi keys
    ∃ executableValue,
      evalPanValueExpCounted state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL expression)
        (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
          some (executableValue,panValueExpStepCost (expOfHOL expression)) ∧
      panValueToHOL executableValue = value := by
  have agree := evalPanValueExpCounted_decodeWithKeys_agree exact ffi hffi keys hkeys expression
  rw [evaluated] at agree
  let state := panSemExecStateOfHOLWithKeys exact ffi keys
  change Option.map (fun result => panValueToHOL result.1)
    (evalPanValueExpCounted state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess state))) = some value at agree
  change ∃ executableValue,
    evalPanValueExpCounted state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
        some (executableValue,panValueExpStepCost (expOfHOL expression)) ∧
    panValueToHOL executableValue = value
  unfold evalPanValueExpCounted at agree ⊢
  cases h : evalPanValueExp state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL expression)
    (memoryAccess := some (panSemBitVec64MemoryAccess state)) with
  | none => simp [h] at agree
  | some v =>
    simp only [h,Option.map_some] at agree
    exact ⟨v,rfl,Option.some.inj agree⟩


/-- Successful HOL argument-list evaluation also retains the exact total
expression-node cost of the executable counted evaluator. -/
theorem evalPanValueExpsCounted_value_and_cost {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (rel : PanSemStateRelExec state exact.toExact) (ranged : PanSemStateRelExecRanged state)
    (expressions : List (Exp (RiscV.Word 64)))
    (byteRanged : ∀ e ∈ expressions, ExpByteRanged e) (values : List (ValueHOL 64))
    (evaluated : exact.evalListHOLFinite (expressions.map expToHOL) = some values) :
    ∃ executableValues,
      evalPanValueExpsCounted state.structs state.locals state.globals state.memory
        state.baseAddress state.topAddress panSemBitVec64BytesInWord expressions
        (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
          some (executableValues,panValueExpsStepCost expressions) ∧
      executableValues.map panValueToHOL = values := by
  have agree := evalPanValueExpsCounted_agree state exact rel ranged expressions byteRanged
  rw [evaluated] at agree
  unfold evalPanValueExpsCounted at agree ⊢
  cases h : evalPanValueExps state.structs state.locals state.globals state.memory
    state.baseAddress state.topAddress panSemBitVec64BytesInWord expressions
    (memoryAccess := some (panSemBitVec64MemoryAccess state)) with
  | none => simp [h] at agree
  | some vs =>
    simp only [h,Option.map_some] at agree
    exact ⟨vs,rfl,Option.some.inj agree⟩

end Flapjack
