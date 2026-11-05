import SteppedFlapjack.StackRawCallSteps.CallReturnSteps
namespace SteppedFlapjack.StackRawCallSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.LoopCase
open Flapjack.Compiler.Backend.StackProps
open SteppedFlapjack.StackSteps

/-- Raw-call optimization does not increase the fine-grained step count. -/
theorem compCorrectMeasureWithinSteps {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F),
      stackSemMeasure p s = measure →
      ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
        (result : Option (StackSemResult width)),
      evaluate (p, s) = (result, post) ∧ result ≠ some .error ∧ stateRel info s target →
      SimulationWithin (compTop info p) info target post result (steps (p, s)) ∧
      SimulationWithin (comp info p) info target post result (steps (p, s)) := by
  intro measure
  induction measure using EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm info t post r hypothesis
  subst hm
  cases p
  case seq first second =>
    apply seqWithinSteps first second info s t post r
    · intro i target out res h
      exact (ih _ (seq_first_measure_lt first second s) first s rfl i target out res h).2
    · intro middle firstRun i target out res h
      have bound := StackSemEvaluateClock.evaluateClock first s none middle firstRun
      exact (ih _ (lexNat_of_le_of_size_lt bound (seq_second_size_lt first second))
        second middle rfl i target out res h).2
    · exact hypothesis
  case ite cmp reg operand first second =>
    apply ifWithinSteps cmp reg operand first second info s t post r
    · intro i target out res h
      exact (ih _ (if_first_measure_lt cmp reg operand first second s) first s rfl i target out res h).2
    · intro i target out res h
      exact (ih _ (if_second_measure_lt cmp reg operand first second s) second s rfl i target out res h).2
    · exact hypothesis
  case loop body =>
    apply loopWithinSteps body info s t post r
    · intro i target out res h
      exact (ih _ (loop_body_measure_lt body s) body s rfl i target out res h).2
    · intro bodyResult middle bodyRun continues nonzero i target out res h
      have lower := loopReentryClockLess body s middle bodyResult bodyRun nonzero
      exact (ih _ (lexNat_of_clock_lt lower) (.loop body) (decClock middle) rfl i target out res h).2
    · exact hypothesis
  case jumpLower r1 r2 dest =>
    apply jumpLowerWithinSteps r1 r2 dest info s t post r
    · intro x y prog left right compared lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero)
        prog (decClock s) rfl i target out res h).1
    · exact hypothesis
  case rawCall dest =>
    apply rawCallWithinSteps dest info s t post r
    · intro first body lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt body (.rawCall dest) s nonzero)
        body (decClock s) rfl i target out res h).2
    · exact hypothesis
  case call ret dest handler =>
    cases ret with
    | none =>
      apply callTailWithinSteps dest handler info s t post r
      · intro absent prog lookup nonzero i target out res h
        exact (ih _ (callee_measure_lt prog (.call none dest handler) s nonzero)
          prog (decClock s) rfl i target out res h).1
      · exact hypothesis
    | some triple =>
      obtain ⟨body, link, l1, l2⟩ := triple
      apply callReturnWithinSteps body link l1 l2 dest handler info s t post r
      · intro prog lookup nonzero i target out res h
        have lower := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) s) nonzero
        exact (ih _ lower prog (decClock (setVar link (.loc l1 l2) s)) rfl i target out res h).1
      · intro prog lookup nonzero middle calleeRun i target out res h
        have bound := StackSemEvaluateClock.evaluateClock prog
          (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
        have lower : middle.clock < s.clock := by
          have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
          exact Nat.lt_of_le_of_lt bound decreased
        exact (ih _ (lexNat_of_clock_lt lower) body middle rfl i target out res h).2
      · intro prog handlerBody hl1 hl2 lookup nonzero present middle calleeRun i target out res h
        have bound := StackSemEvaluateClock.evaluateClock prog
          (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
        have lower : middle.clock < s.clock := by
          have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
          exact Nat.lt_of_le_of_lt bound decreased
        exact (ih _ (lexNat_of_clock_lt lower) handlerBody middle rfl i target out res h).2
      · exact hypothesis
  all_goals exact leafWithinSteps _ s t post info r rfl hypothesis
/-- The two raw-call compiler modes simulate a source run without increasing
its fine-grained step count. -/
theorem compCorrectWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (h : evaluate (p, source) = (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationWithin (compTop info p) info target post result (steps (p, source)) ∧
    SimulationWithin (comp info p) info target post result (steps (p, source)) :=
  compCorrectMeasureWithinSteps _ p source rfl info target post result h
end SteppedFlapjack.StackRawCallSteps
