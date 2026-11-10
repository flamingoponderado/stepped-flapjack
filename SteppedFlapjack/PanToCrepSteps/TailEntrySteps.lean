import SteppedFlapjack.PanToCrepSteps.ControlSteps
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-! Visit counting for the tail-call entry emitted by global lowering. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- The global entry uses the same visit counter as every other source program. -/
noncomputable def globalEntrySteps {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (name : MlString) (args : List (ExpHOL width))
    (s : PanSemStateFiniteExact width σ) : Nat :=
  controlSteps (.seq init (.call none name args)) s

/-- Once initialization and lookup succeed, a source-program bound on the
callee yields a bound for the actual global-entry control-flow shape. -/
theorem globalEntrySteps_bound {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (name : MlString) (args : List (ExpHOL width))
    (s post : PanSemStateFiniteExact width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (locals : HolFiniteMapExact MlString (ValueHOL width))
    (shape : ShapeHOL) (limit : Nat)
    (initRun : s.evaluateHOLFiniteState init = (none,post))
    (arguments : @evalListHOLFinite width σ _ post (fun a => Classical.propDecidable (post.memaddrs a)) args = some values)
    (lookup : lookupCodeHOLFinite post.code.lookup name values = some (body,locals,shape))
    (clock : post.clock ≠ 0)
    (bodyBound : controlSteps body (callEntryStateHOLFinite post locals) ≤ limit) :
    globalEntrySteps init name args s ≤ controlSteps init s + limit + 2 := by
  rw [globalEntrySteps,controlSteps_seq,initRun]
  dsimp only
  rw [controlSteps_tailCall name args post values body locals shape arguments lookup clock]
  omega

/-- A successfully initialized tail entry evaluates its actual callee and
returns its result while the entry counter includes the callee's visits. -/
theorem globalEntry_return_with_steps {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (name : MlString) (args : List (ExpHOL width))
    (s post final : PanSemStateFiniteExact width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (locals : HolFiniteMapExact MlString (ValueHOL width))
    (shape : ShapeHOL) (value : ValueHOL width) (limit : Nat)
    (initRun : s.evaluateHOLFiniteState init = (none,post))
    (arguments : @evalListHOLFinite width σ _ post (fun a => Classical.propDecidable (post.memaddrs a)) args = some values)
    (lookup : lookupCodeHOLFinite post.code.lookup name values = some (body,locals,shape))
    (clock : post.clock ≠ 0)
    (bodyRun : (callEntryStateHOLFinite post locals).evaluateHOLFiniteState body = (some (.returned value),final))
    (shapeMatch : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (bodyBound : controlSteps body (callEntryStateHOLFinite post locals) ≤ limit) :
    s.evaluateHOLFiniteState (.seq init (.call none name args)) = (some (.returned value),emptyLocalsHOLFinite final) ∧
    globalEntrySteps init name args s ≤ controlSteps init s + limit + 2 := by
  constructor
  · rw [evaluateHOLFiniteState_seq_line780,initRun]
    exact evaluateHOLFiniteState_call_return_none post value name args values body locals shape final
      arguments lookup clock bodyRun shapeMatch
  · exact globalEntrySteps_bound init name args s post values body locals shape limit initRun arguments lookup clock bodyBound

/-- A final FFI result from the reached callee propagates through the real
tail-call entry with the same explicit control-visit bound. -/
theorem globalEntry_ffi_with_steps {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (name : MlString) (args : List (ExpHOL width))
    (s post final : PanSemStateFiniteExact width σ) (values : List (ValueHOL width))
    (body : ProgHOL width) (locals : HolFiniteMapExact MlString (ValueHOL width))
    (shape : ShapeHOL) (event : HolFinalEvent) (limit : Nat)
    (initRun : s.evaluateHOLFiniteState init = (none,post))
    (arguments : @evalListHOLFinite width σ _ post (fun a => Classical.propDecidable (post.memaddrs a)) args = some values)
    (lookup : lookupCodeHOLFinite post.code.lookup name values = some (body,locals,shape))
    (clock : post.clock ≠ 0)
    (bodyRun : (callEntryStateHOLFinite post locals).evaluateHOLFiniteState body = (some (.finalFfi event),final))
    (bodyBound : controlSteps body (callEntryStateHOLFinite post locals) ≤ limit) :
    s.evaluateHOLFiniteState (.seq init (.call none name args)) = (some (.finalFfi event),emptyLocalsHOLFinite final) ∧
    globalEntrySteps init name args s ≤ controlSteps init s + limit + 2 := by
  constructor
  · rw [evaluateHOLFiniteState_seq_line780,initRun]
    exact evaluateHOLFiniteState_call_body_fallback post none name args values body locals shape (.finalFfi event) final
      arguments lookup clock bodyRun (Or.inr (Or.inr ⟨event,rfl⟩))
  · exact globalEntrySteps_bound init name args s post values body locals shape limit initRun arguments lookup clock bodyBound

end SteppedFlapjack.PanToCrepSteps
