import SteppedFlapjack.Pancake.Semantics.PanSem.ExpressionCostBridge
import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.PanValueFfiSemantics

/-! A statement-level bridge for scalar returns. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- A successful word-valued HOL expression gives a counted executable return
with the same word; its full statement-and-expression count bounds the HOL
return's control visit. -/
theorem counted_return_word {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys)
    (expression : ExpHOL 64) (word : BitVec 64)
    (evaluated : exact.evalHOLFinite expression = some (.val (.word word)))
    (context : PanValueFfiContext (BitVec 64)) (primitive : PanPrimitiveHandler (BitVec 64))
    (handler : PanValueStatefulFfiHandler (BitVec 64) σ)
    (functions : List (FunName × List VarName × Prog (BitVec 64))) (fuel : Nat) :
    let state := panSemExecStateOfHOLWithKeys exact ffi keys
    evalPanValueFfiProgSteps context primitive handler state.structs functions
      state.baseAddress state.topAddress panSemBitVec64BytesInWord (fuel + 1)
      state.locals state.globals state.memory state.ffi (.return (expOfHOL expression))
      (memoryAccess := some (panSemBitVec64MemoryAccess state)) =
        some (.returned (fun _ => none) state.globals state.memory state.ffi [.word word],
          panValueExpStepCost (expOfHOL expression) + 1) ∧
    exact.evaluateHOLFiniteState (.return expression) =
      (some (.returned (.val (.word word))),PanSemStateFiniteExact.emptyLocalsHOLFinite exact) ∧
    controlSteps (.return expression) exact ≤ panValueExpStepCost (expOfHOL expression) + 1 := by
  obtain ⟨v,evalCounted,hvalue⟩ :=
    evalPanValueExpCounted_decodeWithKeys_value_and_cost exact ffi hffi keys hkeys expression (.val (.word word)) evaluated
  have same : v = .word word := by
    cases v with
    | word bits => simpa using hvalue
    | rStruct fields => simp at hvalue
    | nStruct name fields => simp at hvalue
  subst v
  constructor
  · simp [evalPanValueFfiProgSteps,panValueReturnResult,evalCounted,
      panValuePayloadWithinLimit,panValuePayloadSizeFuel]
  · constructor
    · rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return]
      have hexact : @evalHOLExact 64 σ _ exact.toExact
          (fun address => Classical.propDecidable (exact.memaddrs address)) expression = some (.val (.word word)) := by
        convert evaluated using 1
        unfold PanSemStateFiniteExact.evalHOLFinite
        congr 1
      simp [hexact,shapeOfHOLExact]
    · rw [controlSteps.eq_def]
      simp only
      omega

end SteppedFlapjack.PanToCrepSteps
