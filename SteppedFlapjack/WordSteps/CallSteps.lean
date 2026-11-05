import SteppedFlapjack.WordSteps.Defs
namespace SteppedFlapjack.WordSteps
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Entering a returning call decreases the evaluator measure. -/
theorem returningCalleeMeasure {width : Nat} [NeZero width] {C F : Type}
    (outer callee : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (values : List (WordLocW width)) (ss : Option Nat) (hclock : s.clock ≠ 0) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      ((callEnv values ss (pushEnv envs handler (decClock s))).termdep,
       (callEnv values ss (pushEnv envs handler (decClock s))).clock, sizeOf callee)
      (s.termdep, s.clock, sizeOf outer) := by
  apply wordSemLex
  right
  simp only [WordSemStateFiniteExact.callEnv, pushEnv_clock, pushEnv_termdep, decClock]
  constructor
  · trivial
  · left; omega

/-- A normal return continuation is at a smaller evaluator clock. -/
theorem returnContinuationMeasure {width : Nat} [NeZero width] {C F : Type}
    (outer callee continuation : WordLangProgHOL (BitVec width)) (s middle restored : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (values ys : List (WordLocW width)) (ss : Option Nat) (names : List Nat)
    (res : Option (WordSemResult width)) (hclock : s.clock ≠ 0)
    (run : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) = (res, middle))
    (pop : popEnv middle = some restored) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      ((setVars names ys restored).termdep, (setVars names ys restored).clock, sizeOf continuation)
      (s.termdep, s.clock, sizeOf outer) := by
  obtain ⟨hc, ht⟩ := evaluate_clock callee _ res middle run
  have hp := popEnv_clock _ _ pop
  have hd := popEnv_termdep _ _ pop
  apply wordSemLex
  right
  simp only [WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.callEnv,
    pushEnv_clock, pushEnv_termdep, decClock] at *
  constructor <;> omega

/-- An exception continuation is also at a smaller evaluator clock. -/
theorem exceptionContinuationMeasure {width : Nat} [NeZero width] {C F : Type}
    (outer callee continuation : WordLangProgHOL (BitVec width)) (s middle : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (values : List (WordLocW width)) (ss : Option Nat) (name : Nat) (value : WordLocW width)
    (res : Option (WordSemResult width)) (hclock : s.clock ≠ 0)
    (run : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) = (res, middle)) :
    Prod.Lex (fun a b : Nat => a < b) (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b))
      ((setVar name value middle).termdep, (setVar name value middle).clock, sizeOf continuation)
      (s.termdep, s.clock, sizeOf outer) := by
  obtain ⟨hc, ht⟩ := evaluate_clock callee _ res middle run
  apply wordSemLex
  right
  simp only [WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.callEnv,
    pushEnv_clock, pushEnv_termdep, decClock] at *
  constructor <;> omega

/-- A matching normal return visits the callee and its return continuation. -/
theorem steps_call_return {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s middle restored : WordSemStateFiniteExact width C F)
    (xs values ys : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (run : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) =
      (some (.result (.loc l1 l2) ys), middle)) (hlen : ys.length = names.length)
    (pop : popEnv middle = some restored) (hdom : sptDomainEqUnion restored.locals envs.1 envs.2) :
    steps (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s =
      1 + steps callee (callEnv values ss (pushEnv envs handler (decClock s))) +
        steps continuation (setVars names ys restored) := by
  have hc := returningCalleeMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args handler)
    callee s envs handler values ss hclock
  have hr := returnContinuationMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args handler)
    callee continuation s middle restored envs handler values ys ss names _ hclock run pop
  rw [steps.eq_def]
  simp only [hargs, hbad, Bool.false_eq_true, if_false, hfind, if_neg hvalid, hcut, if_neg hclock, dif_pos hc]
  rw [fix_clock_evaluate, run]
  simp only [hlen, ne_eq, not_true_eq_false, or_false, if_false, pop, if_pos hdom, dif_pos hr]
  omega


/-- A matching exception visits the callee and its exception continuation. -/
theorem steps_call_exception {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (v : Nat) (hprog : WordLangProgHOL (BitVec width)) (hl1 hl2 : Nat)
    (s middle : WordSemStateFiniteExact width C F)
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (value : WordLocW width)
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (run : evaluate callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) =
      (some (.exception (.loc hl1 hl2) value), middle))
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2) :
    steps (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) s =
      1 + steps callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) +
        steps hprog (setVar v value middle) := by
  have hc := returningCalleeMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2)))
    callee s envs (some (v, hprog, hl1, hl2)) values ss hclock
  have hh := exceptionContinuationMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2)))
    callee hprog s middle envs (some (v, hprog, hl1, hl2)) values ss v value _ hclock run
  rw [steps.eq_def]
  simp only [hargs, hbad, Bool.false_eq_true, if_false, hfind, if_neg hvalid, hcut, if_neg hclock, dif_pos hc]
  rw [fix_clock_evaluate, run]
  simp only [ne_eq, not_true_eq_false, if_false, if_pos hdom, dif_pos hh]
  omega


/-- A returning call counts its callee and whichever continuation is actually
selected by the callee result. -/
theorem steps_call_returning {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s middle : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (run : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) = (res, middle)) :
    steps (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s =
      1 + steps callee (callEnv values ss (pushEnv envs handler (decClock s))) +
      match res with
      | some (.result x ys) =>
          if x ≠ .loc l1 l2 ∨ ys.length ≠ names.length then 0 else
          match popEnv middle with
          | none => 0
          | some restored => if sptDomainEqUnion restored.locals envs.1 envs.2 then
              steps continuation (setVars names ys restored) else 0
      | some (.exception x y) =>
          match handler with
          | none => 0
          | some (v, hprog, hl1, hl2) =>
              if x ≠ .loc hl1 hl2 then 0 else
              if sptDomainEqUnion middle.locals envs.1 envs.2 then steps hprog (setVar v y middle) else 0
      | _ => 0 := by
  have hc := returningCalleeMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args handler)
    callee s envs handler values ss hclock
  rw [steps.eq_def]
  simp only [hargs, hbad, Bool.false_eq_true, if_false, hfind, if_neg hvalid, hcut, if_neg hclock, dif_pos hc]
  rw [fix_clock_evaluate]
  conv =>
    lhs
    rw [run]
  cases res with
  | none => simp
  | some r =>
    cases r with
    | result x ys =>
      by_cases hm : x ≠ .loc l1 l2 ∨ ys.length ≠ names.length
      · simp [hm]
      · simp only [hm, if_false]
        cases hp : popEnv middle with
        | none => simp
        | some restored =>
          by_cases hd : sptDomainEqUnion restored.locals envs.1 envs.2
          · have hh := returnContinuationMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args handler)
              callee continuation s middle restored envs handler values ys ss names _ hclock run hp
            simp only [if_pos hd, dif_pos hh]
            omega
          · simp [hd]
    | exception x y =>
      cases handler with
      | none => simp
      | some triple =>
        obtain ⟨v, hprog, hl1, hl2⟩ := triple
        by_cases hx : x ≠ .loc hl1 hl2
        · simp [hx]
        · simp only [hx, if_false]
          by_cases hd : sptDomainEqUnion middle.locals envs.1 envs.2
          · have hh := exceptionContinuationMeasure (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2)))
              callee hprog s middle envs (some (v, hprog, hl1, hl2)) values ss v y _ hclock run
            simp only [if_pos hd, dif_pos hh]
            omega
          · simp [hd]
    | _ => simp

end SteppedFlapjack.WordSteps
