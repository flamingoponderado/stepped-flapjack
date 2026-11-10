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

/-- A declaration counts its body exactly when its initializer evaluates. -/
theorem steps_dec {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width σ) :
    steps (.dec name value body) s = 1 +
      match evalCrepSemHOLExp s value with
      | some v => steps body (CrepSemHOLState.setVar name v s)
      | none => 0 := by
  rw [steps.eq_def]
  have smaller : ∀ v, Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((CrepSemHOLState.setVar name v s).clock,sizeOf body)
      (s.clock,sizeOf (.dec name value body : CrepProgHOL width)) := by
    intro v
    simp only [CrepSemHOLState.setVar]
    apply Prod.Lex.right
    simp_wf
    omega
  simp only [dif_pos (smaller _)]

/-- A continuing loop counts its body and each reached re-entry. -/
theorem steps_while {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (body : CrepProgHOL width)
    (s : CrepSemHOLState width σ) :
    steps (.while condition body) s = 1 +
      match evalCrepSemHOLExp s condition with
      | some (.word w) => if w ≠ 0 ∧ s.clock ≠ 0 then
          let entry := decClockCrepSemHOL s
          steps body entry + match evalCrepSemHOLProgExact entry body with
          | (none,t) | (some (.continue 0),t) => steps (.while condition body) t
          | _ => 0
        else 0
      | _ => 0 := by
  rw [steps.eq_def]
  dsimp only
  rcases evalCrepSemHOLExp s condition with _ | ⟨w⟩ <;> simp only
  by_cases guard : w.1 ≠ 0 ∧ s.clock ≠ 0 <;> try simp only [if_neg guard]
  have bodySmaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((decClockCrepSemHOL s).clock,sizeOf body)
      (s.clock,sizeOf (.while condition body : CrepProgHOL width)) := by
    apply Prod.Lex.left
    simp only [decClockCrepSemHOL]
    omega
  simp only [dif_pos bodySmaller]
  rcases run : evalCrepSemHOLProgExact (decClockCrepSemHOL s) body with ⟨res,t⟩
  have hc := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
  rw [run] at hc
  have loopSmaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (t.clock,sizeOf (.while condition body : CrepProgHOL width))
      (s.clock,sizeOf (.while condition body : CrepProgHOL width)) := by
    apply Prod.Lex.left
    simp only [decClockCrepSemHOL] at hc
    omega
  cases res with
  | none => simp only [dif_pos loopSmaller]
  | some result =>
    cases result <;> try rfl
    case «continue» label =>
      cases label <;> simp only [dif_pos loopSmaller]

/-- A successful tail call counts the exact callee execution. -/
theorem steps_call_tail {width : Nat} [NeZero width] {σ : Type}
    (function : Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (parameters : List Nat) (body : CrepProgHOL width)
    (evaluated : args.mapM (evalCrepSemHOLExp s) = some values)
    (found : s.code.lookup function = some (parameters,body))
    (arity : parameters.length = values.length) (distinct : parameters.Nodup)
    (nonzero : s.clock ≠ 0) :
    steps (.call none function args) s = 1 + steps body
      (decClockCrepSemHOL {s with locals :=
        HolFiniteMapExact.empty.updateList (parameters.zip values)}) := by
  rw [steps.eq_def]
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((decClockCrepSemHOL {s with locals :=
        HolFiniteMapExact.empty.updateList (parameters.zip values)}).clock,sizeOf body)
      (s.clock,sizeOf (.call none function args : CrepProgHOL width)) := by
    apply Prod.Lex.left
    simp only [decClockCrepSemHOL]
    omega
  simp only [evaluated,found,arity,distinct, true_and, dif_pos smaller]
  simp only [if_pos nonzero]
  let env := HolFiniteMapExact.empty.updateList (parameters.zip values)
  rcases evalCrepSemHOLProgExact (decClockCrepSemHOL {s with locals := env}) body with ⟨res,t⟩
  cases res with
  | none => simp only [Nat.add_zero]
  | some result => cases result <;> simp only [Nat.add_zero]

/-- A non-tail call without an exception handler counts its reached callee. -/
theorem steps_call_returning {width : Nat} [NeZero width] {σ : Type}
    (names : List Nat) (function : Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width))
    (s : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (parameters : List Nat) (body : CrepProgHOL width)
    (evaluated : args.mapM (evalCrepSemHOLExp s) = some values)
    (found : s.code.lookup function = some (parameters,body))
    (arity : parameters.length = values.length) (distinct : parameters.Nodup)
    (namesDistinct : names.Nodup) (nonzero : s.clock ≠ 0) :
    steps (.call (some (names,none)) function args) s = 1 + steps body
      (decClockCrepSemHOL {s with locals :=
        HolFiniteMapExact.empty.updateList (parameters.zip values)}) := by
  rw [steps.eq_def]
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      ((decClockCrepSemHOL {s with locals :=
        HolFiniteMapExact.empty.updateList (parameters.zip values)}).clock,sizeOf body)
      (s.clock,sizeOf (.call (some (names,none)) function args : CrepProgHOL width)) := by
    apply Prod.Lex.left
    simp only [decClockCrepSemHOL]
    omega
  simp only [evaluated,found,arity,distinct,namesDistinct, true_and,dif_pos smaller]
  simp only [if_pos nonzero]
  let env := HolFiniteMapExact.empty.updateList (parameters.zip values)
  rcases evalCrepSemHOLProgExact (decClockCrepSemHOL {s with locals := env}) body with ⟨res,t⟩
  cases res with
  | none => simp only [Nat.add_zero]
  | some result => cases result <;> simp only [Nat.add_zero]

end SteppedFlapjack.CrepSteps
