import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateInd

/-! Count LoopSem evaluator nodes along the actual exact execution. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm

/-- Count each visited LoopSem statement once, including calls and the
continuations actually selected by the exact evaluator. -/
noncomputable def steps {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) : Nat :=
  let visit : HolLoopProg width → LoopSemStateFiniteExact width F → Nat := fun q t =>
    if _h : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf q) (s.clock,sizeOf p) then steps q t else 0
  1 + match p with
  | .seq a b => visit a s + match fixClock s (evaluate a s) with
      | (none,t) => visit b t
      | _ => 0
  | .ite cmp r ri a b _ =>
      match sptLookup r s.locals, getVarImm ri s with
      | some (.word x), some (.word y) => if wordCmpHOL cmp x y then visit a s else visit b s
      | _, _ => 0
  | .mark body => visit body s
  | .loop live body _ =>
      match cutRes live (none,s) with
      | (none,t) => visit body t + match fixClock t (evaluate body t) with
          | (none,u) | (some (.continue 0),u) => visit p u
          | _ => 0
      | _ => 0
  | .call ret dest args handler =>
      match getVars args s with
      | none => 0
      | some values =>
        match findCode dest values s.code with
        | none => 0
        | some (env,body) =>
          match ret with
          | none => if handler.isSome || s.clock == 0 then 0 else visit body {decClock s with locals := env}
          | some (names,live) =>
            if ¬ names.Nodup then 0 else
            match cutRes live (none,s) with
            | (none,t) =>
              let entry := {t with locals := env}
              visit body entry + match fixClock entry (evaluate body entry) with
              | (some (.result values),post) =>
                if values.length ≠ names.length then 0 else
                match handler with
                | none => 0
                | some (_,_,cont,_) => visit cont (setVars names values {post with locals := t.locals})
              | (some (.exception value),post) =>
                match handler with
                | none => 0
                | some (v,h,_,_) => visit h (setVar v value {post with locals := t.locals})
              | _ => 0
            | _ => 0
  | _ => 0
termination_by (s.clock,sizeOf p)
decreasing_by all_goals exact _h

/-- Every evaluation includes its root statement. -/
theorem steps_pos {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) : 1 ≤ steps p s := by
  rw [steps.eq_def]
  exact Nat.le_add_right _ _


/-- A nonrecursive statement costs one evaluator visit. -/
theorem steps_leaf {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (h : match p with | .seq _ _ | .ite _ _ _ _ _ _ | .mark _ | .loop _ _ _ | .call _ _ _ _ => false | _ => true) :
    steps p s = 1 := by
  rw [steps.eq_def]
  cases p <;> simp_all

/-- A sequence counts its first execution and its second only when reached. -/
theorem steps_seq {width : Nat} [NeZero width] {F : Type}
    (a b : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    steps (.seq a b) s = 1 + steps a s + match evaluate a s with
      | (none,t) => steps b t
      | _ => 0 := by
  rw [steps.eq_def]
  have first : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf a) (s.clock,sizeOf (.seq a b : HolLoopProg width)) := by
    apply lexLt (Nat.le_refl _); simp_wf; try omega
  simp only [dif_pos first,fix_clock_evaluate]
  rcases run : evaluate a s with ⟨res,t⟩
  cases res with
  | none =>
    have hc := evaluate_clock a s none t run
    have second : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf b) (s.clock,sizeOf (.seq a b : HolLoopProg width)) := by
      apply lexLt hc; simp_wf; omega
    simp only [dif_pos second]
    omega
  | some r => simp only; omega

/-- A mark visits its marked body without changing state. -/
theorem steps_mark {width : Nat} [NeZero width] {F : Type}
    (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    steps (.mark body) s = 1 + steps body s := by
  rw [steps.eq_def]
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf body) (s.clock,sizeOf (.mark body : HolLoopProg width)) := by
    apply lexLt (Nat.le_refl _); simp_wf; try omega
  simp only [dif_pos smaller]

/-- A conditional counts the selected branch after a successful comparison. -/
theorem steps_ite {width : Nat} [NeZero width] {F : Type}
    (cmp : Cmp) (r : Nat) (ri : Flapjack.RegImm (BitVec width))
    (a b : HolLoopProg width) (live : NumSet) (s : LoopSemStateFiniteExact width F) :
    steps (.ite cmp r ri a b live) s = 1 +
      match sptLookup r s.locals, getVarImm ri s with
      | some (.word x), some (.word y) => if wordCmpHOL cmp x y then steps a s else steps b s
      | _, _ => 0 := by
  rw [steps.eq_def]
  have ha : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf a) (s.clock,sizeOf (.ite cmp r ri a b live : HolLoopProg width)) := by
    apply lexLt (Nat.le_refl _); simp_wf; try omega
  have hb : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (s.clock,sizeOf b) (s.clock,sizeOf (.ite cmp r ri a b live : HolLoopProg width)) := by
    apply lexLt (Nat.le_refl _); simp_wf; try omega
  simp only [dif_pos ha,dif_pos hb]


/-- A loop counts the cut body and each actually reached re-entry. -/
theorem steps_loop {width : Nat} [NeZero width] {F : Type}
    (live liveOut : NumSet) (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    steps (.loop live body liveOut) s = 1 +
      match cutRes live (none,s) with
      | (none,t) => steps body t + match evaluate body t with
          | (none,u) | (some (.continue 0),u) => steps (.loop live body liveOut) u
          | _ => 0
      | _ => 0 := by
  rw [steps.eq_def]
  rcases hc : cutRes live (none,s) with ⟨res,t⟩
  cases res with
  | some r => simp [hc]
  | none =>
    have ht := cutRes_none_clock hc
    have hb : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf body) (s.clock,sizeOf (.loop live body liveOut : HolLoopProg width)) := lexLtClock ht
    simp only [hc,dif_pos hb,fix_clock_evaluate]
    rcases he : evaluate body t with ⟨out,u⟩
    have hu := evaluate_clock body t out u he
    have hl : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (u.clock,sizeOf (.loop live body liveOut : HolLoopProg width))
        (s.clock,sizeOf (.loop live body liveOut : HolLoopProg width)) := lexLtClock (by omega)
    change Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (u.clock,1 + sizeOf live + sizeOf body + sizeOf liveOut)
      (s.clock,1 + sizeOf live + sizeOf body + sizeOf liveOut) at hl
    cases out with
    | none => simp only; split <;> rename_i guard <;> first | rfl | exact (guard hl).elim
    | some result =>
      cases result <;> try rfl
      case «continue» label =>
        cases label with
        | zero => simp only; split <;> rename_i guard <;> first | rfl | exact (guard hl).elim
        | succ n => rfl


/-- A successful tail-call lookup counts the reached callee. -/
theorem steps_call_tail {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args : List Nat) (s : LoopSemStateFiniteExact width F)
    (values : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (nonzero : s.clock ≠ 0) :
    steps (.call none dest args none) s = 1 + steps body {decClock s with locals := env} := by
  rw [steps.eq_def]
  have smaller : Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
      (({decClock s with locals := env} : LoopSemStateFiniteExact width F).clock,sizeOf body)
      (s.clock,sizeOf (.call none dest args none : HolLoopProg width)) := by
    apply lexLtClock
    simp only [decClock]
    omega
  simp only [get,found,Option.isSome_none,Bool.false_or,beq_iff_eq,nonzero,if_false,dif_pos smaller]

/-- A reached, successful returning call runs its normal continuation. -/
theorem evaluate_call_returning_success {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live liveOut : NumSet)
    (exception : Nat) (handler normal : HolLoopProg width) (s cut post : LoopSemStateFiniteExact width F)
    (values returned : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (some (.result returned),post))
    (arity : returned.length = names.length) :
    evaluate (.call (some (names,live)) dest args (some (exception,handler,normal,liveOut))) s =
      cutRes liveOut (evaluate normal (setVars names returned {post with locals := cut.locals})) := by
  conv =>
    lhs
    rw [evaluate]
  simp only [get,found,distinct,not_true_eq_false,if_false]
  rw [cutRun]
  simp only
  rw [fix_clock_evaluate,bodyRun]
  simp [arity]

/-- A successful returning call counts the actual callee execution before any
selected continuation. -/
theorem steps_call_returning {width : Nat} [NeZero width] {F : Type}
    (dest : Option Nat) (args names : List Nat) (live : NumSet)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
    (s cut post : LoopSemStateFiniteExact width F) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post)) :
    steps (.call (some (names,live)) dest args handler) s =
      1 + steps body {cut with locals := env} +
      (match out with
      | some (.result returned) =>
        if returned.length ≠ names.length then 0 else
        match handler with
        | none => 0
        | some (_,_,cont,_) => steps cont (setVars names returned {post with locals := cut.locals})
      | some (.exception value) =>
        match handler with
        | none => 0
        | some (v,h,_,_) => steps h (setVar v value {post with locals := cut.locals})
      | _ => 0) := by
  rw [steps.eq_def]
  have cutClock := cutRes_none_clock cutRun
  have bodyClock := evaluate_clock body {cut with locals := env} out post bodyRun
  simp only at bodyClock
  have smaller : ∀ (q : HolLoopProg width) (t : LoopSemStateFiniteExact width F), t.clock < s.clock →
      Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)
        (t.clock,sizeOf q) (s.clock,sizeOf (.call (some (names,live)) dest args handler : HolLoopProg width)) := by
    intro q t h
    exact lexLtClock h
  have entry := smaller body {cut with locals := env} cutClock
  simp only [get,found,distinct,not_true_eq_false,if_false,cutRun,entry,dif_pos]
  simp only [fix_clock_evaluate]
  cases out with
  | none => simp_all
  | some result =>
    cases result <;> try simp_all
    case result returned =>
      by_cases length : returned.length ≠ names.length
      · simp_all
      · cases handler with
        | none => simp_all
        | some h =>
          obtain ⟨v,h,cont,liveOut⟩ := h
          have hm := smaller cont (setVars names returned {post with locals := cut.locals}) (by simp only [setVars]; omega)
          simp_all <;> omega
    case exception value =>
      cases handler with
      | none => simp_all
      | some h =>
        obtain ⟨v,h,cont,liveOut⟩ := h
        have hm := smaller h (setVar v value {post with locals := cut.locals}) (by simp only [setVar]; omega)
        simp_all <;> omega

end SteppedFlapjack.LoopSteps
