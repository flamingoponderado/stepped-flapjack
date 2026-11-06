import SteppedFlapjack.PanToCrepSteps.ControlSteps
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-! Visit counting for the tail-call entry emitted by global lowering. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

open Classical in
/-- Count a tail-call node and, when reached, the call-free callee's control
visits. This counter is intended for a callee in the supported call-free
fragment; `controlSteps` does not recursively count calls or declarations. -/
noncomputable def tailEntrySteps {width : Nat} [NeZero width] {σ : Type}
    (name : MlString) (args : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ) : Nat :=
  1 + match @evalListHOLFinite width σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => 0
  | some values =>
    match lookupCodeHOLFinite s.code.lookup name values with
    | none => 0
    | some (body,locals,_) => if s.clock = 0 then 0 else
        controlSteps body (callEntryStateHOLFinite s locals)

/-- Successful calls include exactly the root visit and the actual reached body. -/
theorem tailEntrySteps_reached {width : Nat} [NeZero width] {σ : Type}
    (name : MlString) (args : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlString (ValueHOL width)) (shape : ShapeHOL)
    (arguments : @evalListHOLFinite width σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (lookup : lookupCodeHOLFinite s.code.lookup name values = some (body,locals,shape))
    (clock : s.clock ≠ 0) :
    tailEntrySteps name args s = 1 + controlSteps body (callEntryStateHOLFinite s locals) := by
  unfold tailEntrySteps
  rw [arguments]
  simp only
  rw [lookup]
  simp only [if_neg clock]

/-- The sequence generated for global initialization includes its own visit,
the reached initializer and, when it succeeds, the reached tail call. -/
noncomputable def globalEntrySteps {width : Nat} [NeZero width] {σ : Type}
    (init : ProgHOL width) (name : MlString) (args : List (ExpHOL width))
    (s : PanSemStateFiniteExact width σ) : Nat :=
  1 + controlSteps init s + match s.evaluateHOLFiniteState init with
    | (none,post) => tailEntrySteps name args post
    | _ => 0

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
  simp only [globalEntrySteps,initRun]
  rw [tailEntrySteps_reached name args post values body locals shape arguments lookup clock]
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

end SteppedFlapjack.PanToCrepSteps
