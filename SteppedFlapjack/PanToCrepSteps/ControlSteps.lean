import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
import SteppedFlapjack.PanToCrepSteps.Shape
import SteppedFlapjack.CrepSteps.BranchStatic

/-! Exact Pancake evaluator visits for the call-free control fragment. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

open Classical in
/-- Counts reached source statements in the call-free control fragment.
Expressions are atomic. Declarations count their reached bodies. Calls are
counted as one and do not include their recursive executions. -/
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
