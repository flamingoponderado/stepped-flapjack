import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
import SteppedFlapjack.PanToCrepSteps.Shape
import SteppedFlapjack.CrepSteps.BranchStatic

/-! Exact Pancake evaluator visits for the call-free control fragment. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

open Classical in
/-- Counts reached source statements in the call-free control fragment.
Expressions are atomic. Calls and declarations are outside this fragment and
are counted as one; this is not a count of their recursive executions. -/
noncomputable def controlSteps {width : Nat} [NeZero width] {σ : Type}
    (p : ProgHOL width) (s : PanSemStateFiniteExact width σ) : Nat :=
  let visit : ProgHOL width → PanSemStateFiniteExact width σ → Nat := fun q t =>
    if _h : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf q) (s.clock,sizeOf p) then controlSteps q t else 0
  1 + match p with
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
