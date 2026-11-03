module

public import Flapjack.Pancake.Semantics.PanSem.EvalExecutedBridge
public import SteppedFlapjack.PanValueExpCounted
@[expose] public section

/-!
# HOL agreement for the step-counted expression evaluator

`evalPanValueExpCounted` (`PanValueExpCounted`) pairs the ordinary expression
result with a source step count.  These theorems show that, after discarding
the count, its result agrees with HOL `eval` under the same conditions as
`evalPanValueExp_agree` in `EvalExecutedBridge`.

Flapjack's clocked semantics no longer uses the counted evaluator; these
results belong with the stepped semantics and move with it (issue #1251).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpByteRanged ExpHOL expToHOL expOfHOL expToHOL_expOfHOL)
open Flapjack.Basis.Pure.MlString (ofString)

/-- The counted expression evaluator agrees with HOL: after discarding its
    Flapjack step count and encoding the value, its state-derived RV64 result agrees with HOL evaluation under
    the same representation and byte-range conditions as
    `evalPanValueExp_agree`. This does not claim that the step count is a HOL
    clock or extend the result to the optional no-access compatibility path. -/
theorem evalPanValueExpCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite (expToHOL e) := by
  simpa [evalPanValueExpCounted, Option.map_map, Function.comp_def] using
    evalPanValueExp_agree state exact hrel hranged e he

/-- The counted expression result agrees with the same
    expression-only HOL view after removing the instrumentation count. -/
theorem evalPanValueExpCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (expToHOL e) := by
  simp only [evalPanValueExpCounted, Option.map_map, Function.comp_def]
  change Option.map panValueToHOL
    (evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress panSemBitVec64BytesInWord e
      (memoryAccess := some (panSemBitVec64MemoryAccess state))) = _
  rw [← evalPanSemStateExp_64_eq_previous]
  exact evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged e he

/-- The same constructed finite view covers the counted expression result. -/
theorem evalPanValueExpCounted_finiteView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (ffi : HolFfiState σ)
    (hffi : FfiStateRel state.ffi ffi)
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hfinite : (panSemStateToExact (panSemExecStateWithHolFfi state ffi)
      (panSemMemoryExactOf state.memory) hmem).FiniteSupport)
    (hranged : PanSemStateRelExecRanged state)
    (e : Exp (RiscV.Word 64)) (he : ExpByteRanged e) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord e
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      (panSemFiniteViewOfExec state ffi hmem hfinite).evalHOLFinite (expToHOL e) := by
  exact evalPanValueExpCounted_agree state (panSemFiniteViewOfExec state ffi hmem hfinite)
    (panSemFiniteViewOfExec_rel state ffi hffi hmem hfinite) hranged e he

/-- An expression decoded from the HOL carrier is automatically byte-ranged;
    no separate syntax-rangedness assumption is needed at this boundary. -/
theorem evalPanValueExpCounted_agree_ofHOL {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state) (e : ExpHOL 64) :
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  simpa only [expToHOL_expOfHOL] using
    evalPanValueExpCounted_agree state exact hrel hranged (expOfHOL e)
      (expOfHOL_byteRanged_bridge e)

/-- The executable codec also supplies the preconditions for the counted
    expression evaluator. -/
theorem evalPanValueExpCounted_decodeWithKeys_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (keys : List MlS)
    (hkeys : ∀ key, exact.code.lookup key ≠ none → key ∈ keys) (e : ExpHOL 64) :
    let state := panSemExecStateOfHOLWithKeys exact ffi keys
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  exact evalPanValueExpCounted_agree_ofHOL (panSemExecStateOfHOLWithKeys exact ffi keys) exact
    (panSemExecStateOfHOLWithKeys_rel exact ffi hffi keys hkeys)
    (panSemExecStateOfHOLWithKeys_ranged exact ffi keys) e

/-- The counted evaluator has the same HOL-origin correspondence after
    discarding the instrumentation count. -/
theorem evalPanValueExpCounted_decode_agree {σ : Type}
    (exact : PanSemStateFiniteExact 64 σ)
    [DecidablePred exact.memaddrs] [DecidablePred exact.shMemaddrs]
    (ffi : FfiState σ) (hffi : FfiStateRel ffi exact.ffi) (e : ExpHOL 64) :
    let state := panSemExecStateOfHOL exact ffi
    Option.map (fun result => panValueToHOL result.1)
        (evalPanValueExpCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord (expOfHOL e)
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalHOLFinite e := by
  exact evalPanValueExpCounted_agree_ofHOL (panSemExecStateOfHOL exact ffi) exact
    (panSemExecStateOfHOL_rel exact ffi hffi) (panSemExecStateOfHOL_ranged exact ffi) e

/-- The same correspondence for the counted argument-list evaluator,
    including list evaluation failure. -/
theorem evalPanValueExpsCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (es : List (Exp (RiscV.Word 64))) (he : ∀ e ∈ es, ExpByteRanged e) :
    Option.map (fun result => result.1.map panValueToHOL)
        (evalPanValueExpsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord es
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalListHOLFinite (es.map expToHOL) := by
  have h := evalPanValueExps_eq_evalListHOLExact_of state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state)) exact es
    (fun e hmem => evalPanValueExp_agree state exact hrel hranged e (he e hmem))
  simpa [evalPanValueExpsCounted, evalPanValueExps, Option.map_map, Function.comp_def] using h

/-- Counted named-field evaluation also uses the state-derived memory access;
    field expressions may themselves contain loads or word operations. -/
theorem evalPanValueFieldsCounted_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ) [DecidablePred exact.memaddrs]
    (hrel : PanSemStateRelExec state exact.toExact)
    (hranged : PanSemStateRelExecRanged state)
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (he : ∀ p ∈ fields, ExpByteRanged p.2) :
    Option.map (fun result => result.1.map (fun p => (ofString p.1, panValueToHOL p.2)))
        (evalPanValueFieldsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord fields
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      exact.evalListFieldsHOLFinite (fields.map (fun p => (ofString p.1, expToHOL p.2))) := by
  have h := evalPanValueFields_eq_evalListFieldsHOLExact_of state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state)) exact fields
    (fun p hp => evalPanValueExp_agree state exact hrel hranged p.2 (he p hp))
  simpa [evalPanValueFieldsCounted, Option.map_map, Function.comp_def] using h

/-- Counted call arguments agree with the isolated finite HOL view of the
    production state. As with the single-expression theorem, this requires no
    assumptions about the code map, exception shapes, or FFI. -/
theorem evalPanValueExpsCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (es : List (Exp (RiscV.Word 64))) (he : ∀ e ∈ es, ExpByteRanged e) :
    Option.map (fun result => result.1.map panValueToHOL)
        (evalPanValueExpsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord es
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalListHOLFinite 64 σ _ (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob) (es.map expToHOL) := by
  have h := @evalPanValueExps_eq_evalListHOLExact_of σ state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state))
    (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) es
    (fun e h => by
      simpa [evalPanSemStateExp_64_eq_previous] using
        evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged e (he e h))
  simpa [evalPanValueExpsCounted, evalPanValueExps, Option.map_map, Function.comp_def] using h

/-- Counted named-field expressions agree with the isolated finite HOL view,
    including failures from a field expression. -/
theorem evalPanValueFieldsCounted_isolatedView_agree {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hmem : PanSemMemoryRel state.memaddrs state.memory (panSemMemoryExactOf state.memory))
    (hloc : PanSemByteKeyFiniteSupport state.locals)
    (hglob : PanSemByteKeyFiniteSupport state.globals)
    (hranged : PanSemStateRelExecRanged state)
    (fields : List (FieldName × Exp (RiscV.Word 64)))
    (he : ∀ p ∈ fields, ExpByteRanged p.2) :
    Option.map (fun result => result.1.map (fun p => (ofString p.1, panValueToHOL p.2)))
        (evalPanValueFieldsCounted state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress panSemBitVec64BytesInWord fields
          (memoryAccess := some (panSemBitVec64MemoryAccess state))) =
      @PanSemStateFiniteExact.evalListFieldsHOLFinite 64 σ _
        (panSemExpressionView state hmem hloc hglob)
        (panSemExpressionViewMemDecider state hmem hloc hglob)
        (fields.map (fun p => (ofString p.1, expToHOL p.2))) := by
  have h := @evalPanValueFields_eq_evalListFieldsHOLExact_of σ state.structs state.locals
    state.globals state.memory state.baseAddress state.topAddress
    panSemBitVec64BytesInWord (some (panSemBitVec64MemoryAccess state))
    (panSemExpressionView state hmem hloc hglob)
    (panSemExpressionViewMemDecider state hmem hloc hglob) fields
    (fun p hp => by
      simpa [evalPanSemStateExp_64_eq_previous] using
        evalPanSemStateExp_isolatedView_agree state hmem hloc hglob hranged p.2 (he p hp))
  simpa [evalPanValueFieldsCounted, Option.map_map, Function.comp_def] using h

end Flapjack
