import SteppedFlapjack.WordSteps.CallSteps
import SteppedFlapjack.WordToStackSteps.TailCallSteps

/-! Clock accounting for successful returning WordSem calls. -/
namespace SteppedFlapjack.WordSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordToStackSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A matching normal return consumes at most the caller's counted steps when
the callee and continuation have established clock bounds. -/
theorem returningCall_consumed_from_bounds (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s middle restored post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (xs values ys : List (WordLocW width))
    (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bodyClock : (callEnv values ss (pushEnv envs handler (decClock s))).clock ≤
      (evaluate callee (callEnv values ss (pushEnv envs handler (decClock s)))).2.clock +
        steps callee (callEnv values ss (pushEnv envs handler (decClock s))))
    (contClock : (setVars names ys restored).clock ≤ (evaluate continuation (setVars names ys restored)).2.clock +
      steps continuation (setVars names ys restored))
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) =
      (some (.result (.loc l1 l2) ys), middle)) (hlen : ys.length = names.length)
    (pop : popEnv middle = some restored) (hdom : sptDomainEqUnion restored.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s = (res, post)) :
    s.clock - post.clock ≤ steps (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s := by
  rw [bodyRun] at bodyClock
  have savedClock := popEnv_clock _ _ pop
  rw [evaluate] at run
  simp only [hargs, hbad, Bool.false_eq_true, if_false, hfind, if_neg hvalid, hcut,
    dif_neg hclock] at run
  rw [fix_clock_evaluate, bodyRun] at run
  simp only [hlen, ne_eq, not_true_eq_false, or_false] at run
  rw [pop] at run
  simp only [if_pos hdom, if_false] at run
  rw [run] at contClock
  rw [steps_call_return dest args names cuts continuation l1 l2 handler s middle restored xs values ys ss callee envs
    hargs hbad hfind hvalid hcut hclock bodyRun hlen pop hdom]
  have entryClock : (callEnv values ss (pushEnv envs handler (decClock s))).clock = s.clock - 1 := by
    simp only [WordSemStateFiniteExact.callEnv, pushEnv_clock, WordSemStateFiniteExact.decClock]
  rw [entryClock] at bodyClock
  change s.clock - 1 ≤ middle.clock + steps callee (callEnv values ss (pushEnv envs handler (decClock s))) at bodyClock
  change restored.clock ≤ post.clock + steps continuation (setVars names ys restored) at contClock
  omega


/-- A matching normal return consumes at most the caller's counted steps when
both the callee and continuation belong to the proved loop fragment. -/
theorem returningCall_consumed (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s middle restored post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (xs values ys : List (WordLocW width))
    (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (calleeShape : loopWord callee = true) (continuationShape : loopWord continuation = true)
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs handler (decClock s))) =
      (some (.result (.loc l1 l2) ys), middle)) (hlen : ys.length = names.length)
    (pop : popEnv middle = some restored) (hdom : sptDomainEqUnion restored.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s = (res, post)) :
    s.clock - post.clock ≤ steps (.call (some (names, cuts, continuation, l1, l2)) dest args handler) s := by
  exact returningCall_consumed_from_bounds dest args names cuts continuation l1 l2 handler s middle restored post res xs values ys ss callee envs
    (loopWord_consumption callee (callEnv values ss (pushEnv envs handler (decClock s))) calleeShape)
    (loopWord_consumption continuation (setVars names ys restored) continuationShape)
    hargs hbad hfind hvalid hcut hclock bodyRun hlen pop hdom run


/-- The exception path composes established callee and handler bounds. -/
theorem returningCall_exception_consumed_from_bounds (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (v : Nat) (hprog : WordLangProgHOL (BitVec width)) (hl1 hl2 : Nat)
    (s middle post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (value : WordLocW width)
    (bodyClock : (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))).clock ≤
      (evaluate callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s)))).2.clock +
        steps callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))))
    (handlerClock : (setVar v value middle).clock ≤ (evaluate hprog (setVar v value middle)).2.clock +
      steps hprog (setVar v value middle))
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) =
      (some (.exception (.loc hl1 hl2) value), middle))
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) s = (res, post)) :
    s.clock - post.clock ≤ steps (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) s := by
  rw [bodyRun] at bodyClock
  rw [evaluate] at run
  simp only [hargs, hbad, Bool.false_eq_true, if_false, hfind, if_neg hvalid, hcut, dif_neg hclock] at run
  rw [fix_clock_evaluate, bodyRun] at run
  simp only [ne_eq, not_true_eq_false, if_false, if_pos hdom] at run
  rw [run] at handlerClock
  rw [steps_call_exception dest args names cuts continuation l1 l2 v hprog hl1 hl2 s middle xs values ss callee envs value
    hargs hbad hfind hvalid hcut hclock bodyRun hdom]
  have entryClock : (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))).clock = s.clock - 1 := by
    simp only [WordSemStateFiniteExact.callEnv, pushEnv_clock, WordSemStateFiniteExact.decClock]
  rw [entryClock] at bodyClock
  change s.clock - 1 ≤ middle.clock + steps callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) at bodyClock
  change middle.clock ≤ post.clock + steps hprog (setVar v value middle) at handlerClock
  omega

/-- The matching exception-handler path obeys the same clock-consumption bound. -/
theorem returningCall_exception_consumed (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (v : Nat) (hprog : WordLangProgHOL (BitVec width)) (hl1 hl2 : Nat)
    (s middle post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (xs values : List (WordLocW width)) (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (value : WordLocW width)
    (calleeShape : loopWord callee = true) (handlerShape : loopWord hprog = true)
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names, cuts, continuation, l1, l2)) xs)
      s.code s.stackSize = some (values, callee, ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (bodyRun : evaluate callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) =
      (some (.exception (.loc hl1 hl2) value), middle))
    (hdom : sptDomainEqUnion middle.locals envs.1 envs.2)
    (run : evaluate (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) s = (res, post)) :
    s.clock - post.clock ≤ steps (.call (some (names, cuts, continuation, l1, l2)) dest args (some (v, hprog, hl1, hl2))) s := by
  exact returningCall_exception_consumed_from_bounds dest args names cuts continuation l1 l2 v hprog hl1 hl2 s middle post res xs values ss callee envs value
    (loopWord_consumption callee (callEnv values ss (pushEnv envs (some (v, hprog, hl1, hl2)) (decClock s))) calleeShape)
    (loopWord_consumption hprog (setVar v value middle) handlerShape)
    hargs hbad hfind hvalid hcut hclock bodyRun hdom run

end SteppedFlapjack.WordSteps
