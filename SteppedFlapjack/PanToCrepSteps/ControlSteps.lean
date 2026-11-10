import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
import SteppedFlapjack.PanToCrepSteps.Shape
import SteppedFlapjack.CrepSteps.BranchStatic

/-! Exact Pancake evaluator visits for the scalar control and call fragment. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

open Classical in
/-- Counts reached source statements. Expressions are atomic; direct calls without exception handlers and declaration calls include their
reached callee and continuation bodies. -/
noncomputable def controlSteps {width : Nat} [NeZero width] {σ : Type}
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Nat :=
  let visit : ProgHOL width → PanSemStateFiniteExact width σ → Nat := fun q t =>
    if _h : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf q) (s.clock,sizeOf p) then controlSteps q t else 0
  1 + match p with
  | .dec name shape initializer body =>
      match @evalHOLExact width σ _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) initializer with
      | some value => if shapeEqHOL shape (shapeOfHOLExact value) then
          visit body (PanSemStateFiniteExact.setVarHOLFinite name value s) else 0
      | none => 0
  | .seq a b => visit a s + match s.evaluateHOLFiniteState a with
      | (none,t) => visit b t
      | _ => 0
  | .ite e a b =>
      match @evalHOLExact width σ _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) e with
      | some (.val (.word w)) => if w ≠ 0 then visit a s else visit b s
      | _ => 0
  | .while e body =>
      match @evalHOLExact width σ _ s.toExact (fun address => Classical.propDecidable (s.memaddrs address)) e with
      | some (.val (.word w)) => if w ≠ 0 ∧ s.clock ≠ 0 then
          let entry := s.decClockHOLFinite
          visit body entry + match entry.evaluateHOLFiniteState body with
          | (none,t) | (some .continue,t) => visit p t
          | _ => 0
        else 0
      | _ => 0
  | .call none function arguments
  | .call (some (_, none)) function arguments =>
      match @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments with
      | none => 0
      | some values =>
          match lookupCodeHOLFinite s.code.lookup function values with
          | none => 0
          | some (body, locals, _) =>
              if s.clock = 0 then 0 else visit body (callEntryStateHOLFinite s locals)
  | .decCall name shape function arguments continuation =>
      match @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments with
      | none => 0
      | some values =>
          match lookupCodeHOLFinite s.code.lookup function values with
          | none => 0
          | some (body, locals, returnShape) =>
              if s.clock = 0 then 0 else
                let entry := callEntryStateHOLFinite s locals
                let result := entry.evaluateHOLFiniteState body
                let fixed := fixClockHOLFinite entry result
                visit body entry + match result.1 with
                  | some (.returned value) =>
                      if shapeEqHOL (shapeOfHOLExact value) shape &&
                          shapeEqHOL (shapeOfHOLExact value) returnShape then
                        visit continuation (setVarHOLFinite name value {fixed.2 with locals := s.locals})
                      else 0
                  | _ => 0
  | _ => 0
termination_by (s.clock,sizeOf p)
decreasing_by all_goals exact _h

/-- Each execution visits its root. -/
theorem controlSteps_pos {width : Nat} [NeZero width] {σ : Type}
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) : 1 ≤ controlSteps p s := by
  rw [controlSteps.eq_def]
  exact Nat.le_add_right _ _


/-- A successful declaration counts its body in the extended local state. -/
theorem controlSteps_dec {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width)
    (state : PanSemStateFiniteExact width σ) (value : ValueHOL width)
    (evaluated : @evalHOLExact width σ _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) initializer = some value)
    (valid : shapeEqHOL shape (shapeOfHOLExact value) = true) :
    controlSteps (.dec name shape initializer body) state =
      1 + controlSteps body (PanSemStateFiniteExact.setVarHOLFinite name value state) := by
  rw [controlSteps.eq_def]
  have smaller : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      ((PanSemStateFiniteExact.setVarHOLFinite name value state).clock,sizeOf body)
      (state.clock,sizeOf (.dec name shape initializer body : ProgHOL width)) := by
    apply Prod.Lex.right
    simp_wf
  simp only [evaluated,valid,if_true,dif_pos smaller]

/-- A source sequence counts its second statement exactly when it is reached. -/
theorem controlSteps_seq {width : Nat} [NeZero width] {σ : Type}
    (a b : ProgHOL width) (s : PanSemStateFiniteExact width σ) :
    controlSteps (.seq a b) s = 1 + controlSteps a s + match s.evaluateHOLFiniteState a with
      | (none,t) => controlSteps b t
      | _ => 0 := by
  rw [controlSteps.eq_def]
  have first : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (s.clock,sizeOf a) (s.clock,sizeOf (.seq a b : ProgHOL width)) := by
    apply Prod.Lex.right
    simp_wf
    omega
  simp only [dif_pos first]
  rcases run : s.evaluateHOLFiniteState a with ⟨res,t⟩
  cases res with
  | none =>
    have hc := evaluateHOLFiniteState_clock_le s a
    rw [run] at hc
    have second : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
        (t.clock,sizeOf b) (s.clock,sizeOf (.seq a b : ProgHOL width)) := by
      by_cases same : t.clock = s.clock
      · rw [same]; apply Prod.Lex.right; simp_wf
      · apply Prod.Lex.left; simp only at hc; omega
    simp only [dif_pos second]
    omega
  | some r => simp only; omega

/-- A conditional counts the reached branch after evaluating its condition. -/
theorem controlSteps_ite {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (a b : ProgHOL width) (source : PanSemStateFiniteExact width σ) :
    controlSteps (.ite condition a b) source = 1 +
      match @evalHOLExact width σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address)) condition with
      | some (.val (.word w)) => if w ≠ 0 then controlSteps a source else controlSteps b source
      | _ => 0 := by
  rw [controlSteps.eq_def]
  have ha : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (source.clock,sizeOf a) (source.clock,sizeOf (.ite condition a b : ProgHOL width)) := by
    apply Prod.Lex.right; simp_wf; omega
  have hb : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (source.clock,sizeOf b) (source.clock,sizeOf (.ite condition a b : ProgHOL width)) := by
    apply Prod.Lex.right; simp_wf
  simp only [dif_pos ha,dif_pos hb]

/-- A source while counts the body and each reached recursive iteration. -/
theorem controlSteps_while {width : Nat} [NeZero width] {σ : Type}
    (condition : ExpHOL width) (body : ProgHOL width) (source : PanSemStateFiniteExact width σ) :
    controlSteps (.while condition body) source = 1 +
      match @evalHOLExact width σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address)) condition with
      | some (.val (.word w)) => if w ≠ 0 ∧ source.clock ≠ 0 then
          let entry := source.decClockHOLFinite
          controlSteps body entry + match entry.evaluateHOLFiniteState body with
          | (none,t) | (some .continue,t) => controlSteps (.while condition body) t
          | _ => 0
        else 0
      | _ => 0 := by
  rw [controlSteps.eq_def]
  dsimp only
  rcases h : @evalHOLExact width σ _ source.toExact (fun address => Classical.propDecidable (source.memaddrs address)) condition with _ | v <;> try rfl
  cases v with
  | val v =>
    cases v with
    | word w =>
      by_cases guard : w ≠ 0 ∧ source.clock ≠ 0 <;> try simp only [if_neg guard]
      have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
          (source.decClockHOLFinite.clock,sizeOf body)
          (source.clock,sizeOf (.while condition body : ProgHOL width)) := by
        apply Prod.Lex.left
        simp only [PanSemStateFiniteExact.decClockHOLFinite]
        omega
      simp only [dif_pos smaller]
      rcases run : source.decClockHOLFinite.evaluateHOLFiniteState body with ⟨res,t⟩
      have clock := evaluateHOLFiniteState_clock_le source.decClockHOLFinite body
      rw [run] at clock
      have smallerLoop : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
          (t.clock,sizeOf (.while condition body : ProgHOL width))
          (source.clock,sizeOf (.while condition body : ProgHOL width)) := by
        apply Prod.Lex.left
        simp only [PanSemStateFiniteExact.decClockHOLFinite] at clock
        omega
      cases res with
      | none => simp only [dif_pos smallerLoop]
      | some r => cases r <;> simp only [dif_pos smallerLoop]
  | _ => rfl

/-- A direct tail call counts the reached callee, in addition to its call node. -/
theorem controlSteps_tailCall {width : Nat} [NeZero width] {σ : Type}
    (function : MlS) (arguments : List (ExpHOL width)) (s : PanSemStateFiniteExact width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (args : @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,returnShape))
    (clock : s.clock ≠ 0) :
    controlSteps (.call none function arguments) s =
      1 + controlSteps body (callEntryStateHOLFinite s locals) := by
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((callEntryStateHOLFinite s locals).clock,sizeOf body)
      (s.clock,sizeOf (.call none function arguments : ProgHOL width)) := by
    apply Prod.Lex.left
    simp only [callEntryStateHOLFinite]
    omega
  rw [controlSteps.eq_def]
  simp only [args,found,clock,if_false,dif_pos smaller]

/-- A non-tail call without an exception handler counts its reached callee. -/
theorem controlSteps_returningCall {width : Nat} [NeZero width] {σ : Type}
    (destination : Option (VarKind × MlS)) (function : MlS) (arguments : List (ExpHOL width))
    (s : PanSemStateFiniteExact width σ) (values : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (args : @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,returnShape))
    (clock : s.clock ≠ 0) :
    controlSteps (.call (some (destination,none)) function arguments) s =
      1 + controlSteps body (callEntryStateHOLFinite s locals) := by
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((callEntryStateHOLFinite s locals).clock,sizeOf body)
      (s.clock,sizeOf (.call (some (destination,none)) function arguments : ProgHOL width)) := by
    apply Prod.Lex.left
    simp only [callEntryStateHOLFinite]
    omega
  rw [controlSteps.eq_def]
  simp only [args,found,clock,if_false,dif_pos smaller]

/-- An ordinary declaration call counts both the reached callee and its
continuation when the callee returns a value of the expected shapes. -/
theorem controlSteps_decCall_return {width : Nat} [NeZero width] {σ : Type}
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL width))
    (continuation : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (value : ValueHOL width) (post : PanSemStateFiniteExact width σ)
    (args : @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,returnShape))
    (clock : s.clock ≠ 0)
    (run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState body = (some (PanSemResultExact.returned value),post))
    (valid : shapeEqHOL (shapeOfHOLExact value) shape = true)
    (returnValid : shapeEqHOL (shapeOfHOLExact value) returnShape = true) :
    let entry := callEntryStateHOLFinite s locals
    let fixed := fixClockHOLFinite entry (some (PanSemResultExact.returned value),post)
    controlSteps (.decCall name shape function arguments continuation) s =
      1 + controlSteps body entry +
        controlSteps continuation (setVarHOLFinite name value {fixed.2 with locals := s.locals}) := by
  have entrySmall : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((callEntryStateHOLFinite s locals).clock,sizeOf body)
      (s.clock,sizeOf (.decCall name shape function arguments continuation : ProgHOL width)) := by
    apply Prod.Lex.left
    simp only [callEntryStateHOLFinite]
    omega
  have continuationSmall : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((setVarHOLFinite name value {(fixClockHOLFinite (callEntryStateHOLFinite s locals)
        (some (PanSemResultExact.returned value),post)).2 with locals := s.locals}).clock,sizeOf continuation)
      (s.clock,sizeOf (.decCall name shape function arguments continuation : ProgHOL width)) := by
    apply Prod.Lex.left
    have bound := fixClockHOLFinite_clock_le (callEntryStateHOLFinite s locals) (some (PanSemResultExact.returned value),post)
    simp only [setVarHOLFinite,callEntryStateHOLFinite] at bound ⊢
    omega
  rw [controlSteps.eq_def]
  simp only [args,found,clock,if_false,run,valid,returnValid,Bool.true_and,if_true,
    dif_pos entrySmall,dif_pos continuationSmall]
  omega

open Flapjack.PanSemStateFiniteExact in
/-- A terminal callee outcome does not visit a declaration-call continuation. -/
theorem controlSteps_decCall_terminal {width : Nat} [NeZero width] {σ : Type}
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL width))
    (continuation : ProgHOL width) (s : PanSemStateFiniteExact width σ)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (locals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (args : @evalListHOLFinite width σ _ s (fun address => Classical.propDecidable (s.memaddrs address)) arguments = some values)
    (found : lookupCodeHOLFinite s.code.lookup function values = some (body,locals,returnShape))
    (clock : s.clock ≠ 0)
    (run : (callEntryStateHOLFinite s locals).evaluateHOLFiniteState body = (result,post))
    (terminal : ∀ value, result ≠ some (.returned value)) :
    controlSteps (.decCall name shape function arguments continuation) s =
      1 + controlSteps body (callEntryStateHOLFinite s locals) := by
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((callEntryStateHOLFinite s locals).clock,sizeOf body)
      (s.clock,sizeOf (.decCall name shape function arguments continuation : ProgHOL width)) := by
    apply Prod.Lex.left
    simp only [callEntryStateHOLFinite]
    omega
  rw [controlSteps.eq_def]
  simp only [args,found,clock,if_false,run,dif_pos smaller]
  cases result with
  | none => simp
  | some r => cases r <;> simp_all

/-- Actual compiled Crep visits are bounded by a syntax factor times the
Pancake source control visits for each supported loop-free branch. -/
theorem branch_compiled_steps {width : Nat} [NeZero width] {σ τ : Type}
    (context : PanToCrepContextExact width) (p : ProgHOL width) (shape : BranchProgram context p)
    (source : PanSemStateFiniteExact width σ) (target : CrepSemHOLState width τ) :
    CrepSteps.steps (compileProgExactHOLW context p) target ≤
      sizeOf (compileProgExactHOLW context p) * controlSteps p source := by
  have static := CrepSteps.branchProgram_static (branch_compile shape) target
  have positive := controlSteps_pos p source
  nlinarith

end SteppedFlapjack.PanToCrepSteps
