import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-! Counts of WordSem evaluator invocations. Clause equations for returning
calls remain to be established before using this counter in pass composition. -/
namespace SteppedFlapjack.WordSteps
open Flapjack Flapjack.WordSemStateFiniteExact

open Classical in
/-- Count the WordSem evaluation nodes actually visited; intermediate states
are those produced by the original evaluator. -/
noncomputable def steps {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  let st : WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat :=
    fun q t =>
      if _h : Prod.Lex (fun a b : Nat => a < b)
          (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
          (t.termdep, t.clock, sizeOf q) (s.termdep, s.clock, sizeOf p) then steps q t else 0
  1 + match p with
  | .mustTerminate q =>
      if s.termdep = 0 then 0 else
        st q {s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1}
  | .seq a b =>
      st a s + match fixClock s (evaluate a s) with
      | (none, t) => st b t
      | _ => 0
  | .ite cmp r ri a b =>
      match getVar r s, getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => st a s
          | some false => st b s
          | none => 0
      | _, _ => 0
  | .loop names body exitNames =>
      match cutState (names, .ln) s with
      | none => 0
      | some u => st body u +
          match fixClock u (evaluate body u) with
          | (res, v) => if wordSemContLoop res ∧ v.clock ≠ 0 then
              st (wordSemSTOP (.loop names body exitNames)) (decClock v) else 0
  | .call ret dest args handler =>
      match getVars args s with
      | none => 0
      | some xs =>
          if wordSemBadDestArgs dest args then 0 else
          match wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
          | none => 0
          | some (args1, prog, ss) =>
              match ret with
              | none =>
                  match handler with
                  | some _ => 0
                  | none => if s.clock = 0 then 0 else st prog (callEnv args1 ss (decClock s))
              | some (n, names, retHandler, l1, l2) =>
                  if sptDomainEmpty names.1 ∨ ¬ n.Nodup then 0 else
                  match wordSemCutEnvs names s.locals with
                  | none => 0
                  | some envs =>
                    if s.clock = 0 then 0 else
                    let entry := callEnv args1 ss (pushEnv envs handler (decClock s))
                    st prog entry + match fixClock entry (evaluate prog entry) with
                    | (some (.result x ys), s2) =>
                        if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then 0 else
                        match popEnv s2 with
                        | none => 0
                        | some s1 => if sptDomainEqUnion s1.locals envs.1 envs.2 then
                            st retHandler (setVars n ys s1) else 0
                    | (some (.exception x y), s2) =>
                        match handler with
                        | none => 0
                        | some (v, hprog, hl1, hl2) =>
                            if x ≠ .loc hl1 hl2 then 0 else
                            if sptDomainEqUnion s2.locals envs.1 envs.2 then st hprog (setVar v y s2) else 0
                    | _ => 0
  | _ => 0
termination_by (s.termdep, s.clock, sizeOf p)
decreasing_by all_goals exact _h

/-- The constructors that may recursively evaluate another WordSem program. -/
def isRecursive {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Bool
  | .mustTerminate _ | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _ | .call _ _ _ _ => true
  | _ => false

/-- Every WordSem evaluation visits at least its root node. -/
theorem steps_pos {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : 1 ≤ steps p s := by
  rw [steps.eq_def]
  exact Nat.le_add_right _ _

/-- A nonrecursive WordSem node visits exactly one evaluator node. -/
theorem steps_leaf {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hp : isRecursive p = false) : steps p s = 1 := by
  rw [steps.eq_def]
  cases p <;> simp_all [isRecursive]

theorem seqFirstMeasure {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (s.termdep, s.clock, sizeOf a) (s.termdep, s.clock, sizeOf (.seq a b : WordLangProgHOL (BitVec width))) := by
  apply wordSemLex
  right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
  simp_wf
  omega

theorem seqSecondMeasure {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s t : WordSemStateFiniteExact width C F)
    (r : Option (WordSemResult width)) (he : evaluate a s = (r, t)) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (t.termdep, t.clock, sizeOf b) (s.termdep, s.clock, sizeOf (.seq a b : WordLangProgHOL (BitVec width))) := by
  obtain ⟨hc, ht⟩ := evaluate_clock a s r t he
  apply wordSemLex
  right; refine ⟨ht, ?_⟩
  rcases Nat.lt_or_eq_of_le hc with h | h
  · exact Or.inl h
  · right; refine ⟨h, ?_⟩; simp_wf; omega

/-- Sequence counts the first run and, when it continues, the second run. -/
theorem steps_seq {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    steps (.seq a b) s = 1 + steps a s +
      match evaluate a s with
      | (none, t) => steps b t
      | _ => 0 := by
  rw [steps.eq_def]
  simp only [dif_pos (seqFirstMeasure a b s), fix_clock_evaluate]
  rcases he : evaluate a s with ⟨res, t⟩
  cases res with
  | none => simp only [dif_pos (seqSecondMeasure a b s t none he)]; omega
  | some r => simp only; omega


theorem iteFirstMeasure {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (s.termdep, s.clock, sizeOf a) (s.termdep, s.clock, sizeOf (.ite cmp r ri a b : WordLangProgHOL (BitVec width))) := by
  apply wordSemLex
  right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
  simp_wf
  omega

theorem iteSecondMeasure {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (s.termdep, s.clock, sizeOf b) (s.termdep, s.clock, sizeOf (.ite cmp r ri a b : WordLangProgHOL (BitVec width))) := by
  apply wordSemLex
  right; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
  simp_wf
  omega

/-- A conditional counts only its selected branch. -/
theorem steps_ite {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
    (a b : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    steps (.ite cmp r ri a b) s = 1 +
      match getVar r s, getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => steps a s
          | some false => steps b s
          | none => 0
      | _, _ => 0 := by
  rw [steps.eq_def]
  simp only [dif_pos (iteFirstMeasure cmp r ri a b s), dif_pos (iteSecondMeasure cmp r ri a b s)]


theorem loopBodyMeasure {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s u : WordSemStateFiniteExact width C F) (cut : cutState (names, .ln) s = some u) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      (u.termdep, u.clock, sizeOf body) (s.termdep, s.clock, sizeOf (.loop names body exitNames : WordLangProgHOL (BitVec width))) := by
  obtain ⟨hc, ht⟩ := cutState_clock_termdep _ _ _ cut
  apply wordSemLex
  right; refine ⟨ht, Or.inr ⟨hc, ?_⟩⟩
  simp_wf
  omega

theorem loopReentryMeasure {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s u v : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (cut : cutState (names, .ln) s = some u) (run : evaluate body u = (res, v)) (nonzero : v.clock ≠ 0) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      ((decClock v).termdep, (decClock v).clock, sizeOf (wordSemSTOP (.loop names body exitNames : WordLangProgHOL (BitVec width))))
      (s.termdep, s.clock, sizeOf (.loop names body exitNames : WordLangProgHOL (BitVec width))) := by
  obtain ⟨hc, ht⟩ := cutState_clock_termdep _ _ _ cut
  obtain ⟨hec, het⟩ := evaluate_clock body u res v run
  apply wordSemLex
  right
  simp only [decClock]
  constructor
  · omega
  · left; omega

/-- Loop counting follows the original cut, body, and continuing iteration. -/
theorem steps_loop {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    steps (.loop names body exitNames) s = 1 +
      match cutState (names, .ln) s with
      | none => 0
      | some u => steps body u + match evaluate body u with
        | (res, v) => if wordSemContLoop res ∧ v.clock ≠ 0 then
            steps (.loop names body exitNames) (decClock v) else 0 := by
  rw [steps.eq_def]
  cases hc : cutState (names, .ln) s with
  | none => simp only [hc]
  | some u =>
    simp only [hc, dif_pos (loopBodyMeasure names exitNames body s u hc), fix_clock_evaluate]
    rcases he : evaluate body u with ⟨res, v⟩
    by_cases hv : wordSemContLoop res ∧ v.clock ≠ 0
    · have hm := loopReentryMeasure names exitNames body s u v res hc he hv.2
      dsimp only [wordSemSTOP] at hm
      simp [hv.1, hv.2, wordSemSTOP]
      change (if _h : Prod.Lex (fun a b : Nat => a < b)
        (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
        ((decClock v).termdep, (decClock v).clock, sizeOf (.loop names body exitNames : WordLangProgHOL (BitVec width)))
        (s.termdep, s.clock, sizeOf (.loop names body exitNames : WordLangProgHOL (BitVec width)))
        then steps (.loop names body exitNames) (decClock v) else 0) = _
      exact dif_pos hm
    · simp [hv]


/-- Must-terminate evaluates its body exactly when the termination depth is nonzero. -/
theorem steps_mustTerminate {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    steps (.mustTerminate body) s = 1 + if s.termdep = 0 then 0 else
      steps body {s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1} := by
  rw [steps.eq_def]
  by_cases h : s.termdep = 0
  · simp [h]
  · have hm : Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
        (s.termdep - 1, wordSemMustTerminateLimit width, sizeOf body)
        (s.termdep, s.clock, sizeOf (.mustTerminate body : WordLangProgHOL (BitVec width))) := by
      apply wordSemLex
      left; omega
    simp only [h, if_false]
    exact congrArg (1 + ·) (dif_pos hm)


theorem tailCallMeasure {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact width C F)
    (values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (hclock : s.clock ≠ 0) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      ((callEnv values ss (decClock s)).termdep, (callEnv values ss (decClock s)).clock, sizeOf callee)
      (s.termdep, s.clock, sizeOf (.call none dest args none : WordLangProgHOL (BitVec width))) := by
  apply wordSemLex
  right
  simp only [WordSemStateFiniteExact.callEnv, decClock]
  constructor
  · trivial
  · left; omega

/-- A successful tail call visits its callee after the call node. -/
theorem steps_call_tail {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact width C F)
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest xs s.code s.stackSize = some (values, callee, ss))
    (hclock : s.clock ≠ 0) :
    steps (.call none dest args none) s = 1 + steps callee (callEnv values ss (decClock s)) := by
  rw [steps.eq_def]
  simp only [hargs, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hfind, if_neg hclock,
    dif_pos (tailCallMeasure dest args s values ss callee hclock)]


/-- A continuing sequence counts both component executions. -/
theorem steps_seq_run {width : Nat} [NeZero width] {C F : Type}
    (a b : WordLangProgHOL (BitVec width)) (s t : WordSemStateFiniteExact width C F)
    (run : evaluate a s = (none, t)) :
    steps (.seq a b) s = 1 + steps a s + steps b t := by
  rw [steps_seq, run]

end SteppedFlapjack.WordSteps
