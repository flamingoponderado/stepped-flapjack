import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Batteries.Tactic.PermuteGoals
import Mathlib.Data.Nat.Basic
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

/-! A fine-grained step count for StackSem (stepped-flapjack#2, phase C).

`steps (prog, s)` counts the `evaluate` invocations of the StackSem run of
`prog` from `s`: one for the node itself plus the steps of every recursive
`evaluate` call its clause makes, in the clause's order and on the states
`evaluate` computes. The count leaves the semantics untouched: intermediate
states come from Flapjack's `StackSemEvaluate.evaluate`, so no agreement
theorem is needed, and the count is measured on exactly the run the existing
correctness chain uses.

The StackSem clock counts only calls and loop iterations. `steps` also counts
every `Seq`, `If` and leaf node, so a pass that removes statements lowers the
count.

The recursion follows `evaluateHOL`: the guard `LexNat` on HOL's clock-first
measure restricts recursive calls to smaller arguments, and the per-clause
equations below show the guard always holds. -/

namespace SteppedFlapjack.StackSteps

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

open Classical in
/-- The number of `evaluate` invocations of the StackSem run of `p` from `s`. -/
noncomputable def stepsHOL {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  let st : HolProg width → StackSemStateFiniteExact width C F → Nat :=
    fun p' s' =>
      if _h : LexNat (stackSemMeasure p' s') (stackSemMeasure p s) then stepsHOL p' s'
      else 0
  1 + match p with
  | .seq a b =>
      st a s +
        match fixClock s (evaluate (a, s)) with
        | (none, s1) => st b s1
        | _ => 0
  | .ite cmp r ri a b =>
      match getVar r s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => st a s
          | some false => st b s
          | none => 0
      | _, _ => 0
  | .loop body =>
      st body s +
        match fixClock s (evaluate (body, s)) with
        | (res, s1) =>
            if contLoop res ∧ s1.clock ≠ 0 then st (.loop body) (decClock s1) else 0
  | .jumpLower r1 r2 dest =>
      match getVar r1 s, getVar r2 s with
      | some (.word x), some (.word y) =>
          if wordCmpHOL .lower x y then
            match findCode (.inl dest) s.regs s.code with
            | some prog => if s.clock = 0 then 0 else st prog (decClock s)
            | none => 0
          else 0
      | _, _ => 0
  | .rawCall dest =>
      match sptLookup dest s.code with
      | some prog =>
          match destSeq prog with
          | some (_, body) => if s.clock = 0 then 0 else st body (decClock s)
          | none => 0
      | none => 0
  | .call none dest handler =>
      match findCode dest s.regs s.code, handler with
      | some prog, none => if s.clock = 0 then 0 else st prog (decClock s)
      | _, _ => 0
  | .call (some (retH, link, l1, l2)) dest handler =>
      match findCode dest (s.regs.eraseEq link) s.code with
      | none => 0
      | some prog =>
          if s.clock = 0 then 0
          else
            let s' := setVar link (.loc l1 l2) s
            st prog (decClock s') +
              match fixClock (decClock s') (evaluate (prog, decClock s')) with
              | (some (.result x), s2) => if x = .loc l1 l2 then st retH s2 else 0
              | (some (.exception x), s2) =>
                  match handler with
                  | some (h, hl1, hl2) => if x = .loc hl1 hl2 then st h s2 else 0
                  | none => 0
              | _ => 0
  | _ => 0
termination_by stackSemMeasure p s
decreasing_by all_goals exact _h

/-- `steps` with HOL's tupled `(prog, state)` argument, as `evaluate` takes it. -/
noncomputable def steps {width : Nat} [NeZero width] {C F : Type}
    (ps : HolProg width × StackSemStateFiniteExact width C F) : Nat :=
  stepsHOL ps.1 ps.2

/-- A StackSem run that ends with `(r, s2)` within `n` steps. -/
def evaluatesWithin {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n : Nat) : Prop :=
  evaluate (p, s) = (r, s2) ∧ steps (p, s) ≤ n

theorem evaluatesWithin_mono {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {s s2 : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {n m : Nat} (h : evaluatesWithin p s r s2 n)
    (hnm : n ≤ m) : evaluatesWithin p s r s2 m :=
  ⟨h.1, Nat.le_trans h.2 hnm⟩

/-! ### Clause equations -/

theorem steps_pos {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) : 1 ≤ steps (p, s) := by
  unfold steps; rw [stepsHOL.eq_def]; exact Nat.le_add_right _ _

/-- The constructors whose clause makes recursive `evaluate` calls. -/
def isRecursive {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .jumpLower _ _ _ | .rawCall _ | .call _ _ _ => true
  | _ => false

/-- A node without recursive `evaluate` calls takes one step. -/
theorem steps_leaf {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hp : isRecursive p = false) : steps (p, s) = 1 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  cases p <;> simp_all [isRecursive]

theorem steps_seq {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s : StackSemStateFiniteExact width C F) :
    steps ((.seq a b : HolProg width), s) =
      1 + steps (a, s) +
        match fixClock s (evaluate (a, s)) with
        | (none, s1) => steps (b, s1)
        | _ => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  simp only [dif_pos (seq_first_measure_lt a b s)]
  have h2 := seq_second_measure_lt a b s (evaluate (a, s))
  rcases hfx : fixClock s (evaluate (a, s)) with ⟨res, s1⟩
  rw [hfx] at h2
  cases res with
  | none => simp only [dif_pos h2]; omega
  | some r => simp only; omega

theorem steps_ite {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) :
    steps ((.ite cmp r ri a b : HolProg width), s) =
      1 + match getVar r s, StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s with
        | some x, some y =>
            match wordSemWordCmp cmp x y with
            | some true => steps (a, s)
            | some false => steps (b, s)
            | none => 0
        | _, _ => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  simp only [dif_pos (if_first_measure_lt cmp r ri a b s),
    dif_pos (if_second_measure_lt cmp r ri a b s)]

theorem steps_loop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s : StackSemStateFiniteExact width C F) :
    steps ((.loop body : HolProg width), s) =
      1 + steps (body, s) +
        match fixClock s (evaluate (body, s)) with
        | (res, s1) =>
            if contLoop res ∧ s1.clock ≠ 0 then steps (.loop body, decClock s1) else 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  simp only [dif_pos (loop_body_measure_lt body s)]
  have h2 := fun hne => loop_reentry_measure_lt body s (evaluate (body, s)) hne
  rcases hfx : fixClock s (evaluate (body, s)) with ⟨res, s1⟩
  rw [hfx] at h2
  dsimp only
  by_cases hc : contLoop res ∧ s1.clock ≠ 0
  · simp only [if_pos hc, dif_pos (h2 hc.2)]; omega
  · simp only [if_neg hc]; omega

theorem steps_jumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (s : StackSemStateFiniteExact width C F) :
    steps ((.jumpLower r1 r2 dest : HolProg width), s) =
      1 + match getVar r1 s, getVar r2 s with
        | some (.word x), some (.word y) =>
            if wordCmpHOL .lower x y then
              match findCode (.inl dest) s.regs s.code with
              | some prog => if s.clock = 0 then 0 else steps (prog, decClock s)
              | none => 0
            else 0
        | _, _ => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  congr 1
  split
  · split
    · split
      · rename_i prog _
        by_cases h0 : s.clock = 0
        · simp [h0]
        · simp [h0, dif_pos (callee_measure_lt prog (.jumpLower r1 r2 dest) s h0)]
      · rfl
    · rfl
  · rfl

theorem steps_rawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (s : StackSemStateFiniteExact width C F) :
    steps ((.rawCall dest : HolProg width), s) =
      1 + match sptLookup dest s.code with
        | some prog =>
            match destSeq prog with
            | some (_, body) => if s.clock = 0 then 0 else steps (body, decClock s)
            | none => 0
        | none => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  congr 1
  split
  · split
    · rename_i body _
      by_cases h0 : s.clock = 0
      · simp [h0]
      · simp [h0, dif_pos (callee_measure_lt body (.rawCall dest) s h0)]
    · rfl
  · rfl

theorem steps_call_none {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (s : StackSemStateFiniteExact width C F) :
    steps ((.call none dest handler : HolProg width), s) =
      1 + match findCode dest s.regs s.code, handler with
        | some prog, none => if s.clock = 0 then 0 else steps (prog, decClock s)
        | _, _ => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  congr 1
  split
  · rename_i prog hf
    by_cases h0 : s.clock = 0
    · simp [hf, h0]
    · simp [hf, h0, dif_pos (callee_measure_lt prog (.call none dest none) s h0)]
  · rename_i hne
    split
    · rename_i prog hf
      exact (hne prog (by simp_all) (by simp_all)).elim
    · rfl

theorem steps_call_some {width : Nat} [NeZero width] {C F : Type}
    (retH : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (s : StackSemStateFiniteExact width C F) :
    steps ((.call (some (retH, link, l1, l2)) dest handler : HolProg width), s) =
      1 + match findCode dest (s.regs.eraseEq link) s.code with
        | none => 0
        | some prog =>
            if s.clock = 0 then 0
            else
              let s' := setVar link (.loc l1 l2) s
              steps (prog, decClock s') +
                match fixClock (decClock s') (evaluate (prog, decClock s')) with
                | (some (.result x), s2) => if x = .loc l1 l2 then steps (retH, s2) else 0
                | (some (.exception x), s2) =>
                    match handler with
                    | some (h, hl1, hl2) => if x = .loc hl1 hl2 then steps (h, s2) else 0
                    | none => 0
                | _ => 0 := by
  unfold steps; rw [stepsHOL.eq_def]; dsimp only
  congr 1
  split
  · rfl
  · rename_i prog _
    by_cases h0 : s.clock = 0
    · simp [h0]
    · simp only [h0, if_false]
      have hs' : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using h0
      have hpar : stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) s) =
          stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s := by
        simp [stackSemMeasure, setVar]
      have hcallee := callee_measure_lt prog (.call (some (retH, link, l1, l2)) dest handler)
        (setVar link (.loc l1 l2) s) hs'
      rw [hpar] at hcallee
      rw [dif_pos hcallee]
      have hk := fun cont => call_continuation_measure_lt cont
        (.call (some (retH, link, l1, l2)) dest handler) s link l1 l2
        (evaluate (prog, decClock (setVar link (.loc l1 l2) s))) h0
      rcases hfx : fixClock (decClock (setVar link (.loc l1 l2) s))
          (evaluate (prog, decClock (setVar link (.loc l1 l2) s))) with ⟨res, s2⟩
      rw [hfx] at hk
      congr 1
      rcases res with _ | ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _ <;>
        (try rcases handler with _ | ⟨h, hl1, hl2⟩) <;> simp [dif_pos (hk _)]

/-! ### Step equations on runs that succeed

These rewrite the `match`es in the clause equations once the run is known. -/

theorem steps_seq_run {width : Nat} [NeZero width] {C F : Type}
    (a b : HolProg width) (s s1 : StackSemStateFiniteExact width C F)
    (h : StackSemEvaluate.evaluate (a, s) = (none, s1)) :
    steps ((.seq a b : HolProg width), s) = 1 + steps (a, s) + steps (b, s1) := by
  rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, h]

theorem steps_loop_run {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s s1 : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width))
    (h : StackSemEvaluate.evaluate (body, s) = (res, s1))
    (cont : StackSemControl.contLoop res = true) (clock : s1.clock ≠ 0) :
    steps ((.loop body : HolProg width), s) =
      1 + steps (body, s) + steps (.loop body, StackSemStateOps.decClock s1) := by
  rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, h]
  simp only [cont, true_and]
  rw [if_pos clock]

theorem steps_loop_exit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (s s1 : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width))
    (h : StackSemEvaluate.evaluate (body, s) = (res, s1))
    (stop : ¬ (StackSemControl.contLoop res ∧ s1.clock ≠ 0)) :
    steps ((.loop body : HolProg width), s) = 1 + steps (body, s) := by
  rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, h]
  simp only [stop, if_false, Nat.add_zero]

theorem steps_ite_true {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) (x y : WordLocW width)
    (hx : StackSemStateOps.getVar r s = some x)
    (hy : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s = some y)
    (hw : wordSemWordCmp cmp x y = some true) :
    steps ((.ite cmp r ri a b : HolProg width), s) = 1 + steps (a, s) := by
  rw [steps_ite]
  simp only [hx, hy, hw]

theorem steps_ite_false {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : HolRegImm width) (a b : HolProg width)
    (s : StackSemStateFiniteExact width C F) (x y : WordLocW width)
    (hx : StackSemStateOps.getVar r s = some x)
    (hy : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) s = some y)
    (hw : wordSemWordCmp cmp x y = some false) :
    steps ((.ite cmp r ri a b : HolProg width), s) = 1 + steps (b, s) := by
  rw [steps_ite]
  simp only [hx, hy, hw]


end SteppedFlapjack.StackSteps
