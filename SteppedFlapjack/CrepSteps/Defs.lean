import Flapjack.Pancake.Semantics.CrepSem.EvaluateInd

/-! Count exact Crep evaluator visits, including reached callees and handlers. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack

open Classical in
/-- The number of statement evaluations in the exact Crep run. Expressions
are atomic here; their compilation cost must be accounted for separately. -/
noncomputable def steps {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : Nat :=
  let visit : CrepProgHOL width → CrepSemHOLState width σ → Nat := fun q t =>
    if _h : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf q) (s.clock,sizeOf p) then steps q t else 0
  1 + match p with
  | .dec name value body =>
      match evalCrepSemHOLExp s value with
      | some v => visit body (CrepSemHOLState.setVar name v s)
      | none => 0
  | .seq a b => visit a s + match evalCrepSemHOLProgExact s a with
      | (none,t) => visit b t
      | _ => 0
  | .ite condition a b =>
      match evalCrepSemHOLExp s condition with
      | some (.word w) => if w ≠ 0 then visit a s else visit b s
      | _ => 0
  | .while condition body =>
      match evalCrepSemHOLExp s condition with
      | some (.word w) => if w ≠ 0 ∧ s.clock ≠ 0 then
          let entry := decClockCrepSemHOL s
          visit body entry + match evalCrepSemHOLProgExact entry body with
          | (none,t) | (some (.continue 0),t) => visit p t
          | _ => 0
        else 0
      | _ => 0
  | .call ret function args =>
      match args.mapM (evalCrepSemHOLExp s) with
      | none => 0
      | some values =>
        match s.code.lookup function with
        | none => 0
        | some (parameters,body) =>
          if parameters.length = values.length ∧ parameters.Nodup ∧
              (match ret with | none => True | some (names,_) => names.Nodup) ∧
              s.clock ≠ 0 then
            let env := HolFiniteMapExact.empty.updateList (parameters.zip values)
            let entry := decClockCrepSemHOL {s with locals := env}
            visit body entry + match evalCrepSemHOLProgExact entry body, ret with
            | (some (.exception eid),t), some (_,some (expected,handler)) =>
                if eid = expected then visit handler {t with locals := s.locals} else 0
            | _, _ => 0
          else 0
  | _ => 0
termination_by (s.clock,sizeOf p)
decreasing_by all_goals exact _h

/-- Each run visits its root statement. -/
theorem steps_pos {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) : 1 ≤ steps p s := by
  rw [steps.eq_def]
  exact Nat.le_add_right _ _

/-- A nonrecursive statement costs one evaluator visit. -/
theorem steps_leaf {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ)
    (h : match p with | .dec _ _ _ | .seq _ _ | .ite _ _ _ | .while _ _ | .call _ _ _ => false | _ => true) :
    steps p s = 1 := by
  rw [steps.eq_def]
  cases p <;> simp_all

/-- A sequence counts its second statement precisely when it is reached. -/
theorem steps_seq {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (s : CrepSemHOLState width σ) :
    steps (.seq a b) s = 1 + steps a s + match evalCrepSemHOLProgExact s a with
      | (none,t) => steps b t
      | _ => 0 := by
  rw [steps.eq_def]
  have first : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf a) (s.clock,sizeOf (.seq a b : CrepProgHOL width)) := by
    apply Prod.Lex.right
    simp_wf
    omega
  simp only [dif_pos first]
  rcases run : evalCrepSemHOLProgExact s a with ⟨res,t⟩
  cases res with
  | none =>
    have hc := evalCrepSemHOLProgExact_clock_le s a
    rw [run] at hc
    have second : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf b) (s.clock,sizeOf (.seq a b : CrepProgHOL width)) := by
      by_cases eq : t.clock = s.clock
      · rw [eq]; apply Prod.Lex.right; simp_wf; omega
      · apply Prod.Lex.left; simp only at hc; omega
    simp only [dif_pos second]
    omega
  | some r => simp only; omega

/-- A conditional counts only the branch selected by its expression. -/
theorem steps_ite {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (a b : CrepProgHOL width)
    (s : CrepSemHOLState width σ) :
    steps (.ite condition a b) s = 1 +
      match evalCrepSemHOLExp s condition with
      | some (.word w) => if w ≠ 0 then steps a s else steps b s
      | _ => 0 := by
  rw [steps.eq_def]
  have ha : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf a) (s.clock,sizeOf (.ite condition a b : CrepProgHOL width)) := by
    apply Prod.Lex.right; simp_wf; omega
  have hb : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf b) (s.clock,sizeOf (.ite condition a b : CrepProgHOL width)) := by
    apply Prod.Lex.right; simp_wf; omega
  simp only [dif_pos ha,dif_pos hb]

end SteppedFlapjack.CrepSteps
