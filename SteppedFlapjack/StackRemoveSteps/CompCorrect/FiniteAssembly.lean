import SteppedFlapjack.StackRemoveSteps.CompCorrect.Leaf
import SteppedFlapjack.StackRemoveSteps.RunBudget

/-! Stack-removal simulation with finite, computed oracle and bitmap budgets. -/

set_option maxHeartbeats 2000000
namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}
local macro "normalize_step" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, post, run, relation, stepBound⟩
    refine ⟨clock, post, run, ?_, stepBound⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

theorem compCorrectWithinSteps
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) (B K : Nat)
    (Kpos : 1 ≤ K)
    (n : Nat) (hsteps : steps (program, source) ≤ n)
    (cost : leafCost B bounds program ≤ K)
    (hcode : codeBound B bounds K source) (horacle : oraclePrefixBound B bounds K n source)
    (hbitmap : source.bitmaps.length + oracleBitmapBudget n source.compileOracle ≤ B)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer program, {target with clock := clock + target.clock}) ≤
        K * steps (program, source) := by
  by_cases leaf : isRecursive program = false
  · exact compCorrectLeafWithinSteps program source result postSource target pointer bounds jump B K
      (by omega) leaf cost hypothesis
  · revert hypothesis cost leaf
    cases hp : program <;> intro cost hypothesis leaf <;> rw [hp] at hsteps
    all_goals try (simp [isRecursive] at leaf)
    case seq first second =>
      have hfirst : steps (first, source) ≤ n := (steps_seq_first_le first second source).trans hsteps
      refine (by normalize_step result using (compCorrectSeqWithinSteps first second source result postSource target pointer bounds jump B K Kpos ?_ ?_ hypothesis))
      · intro rr post t h
        normalize_step rr using (compCorrectWithinSteps first source rr post t pointer bounds jump B K Kpos n hfirst
          ((leafCost_seq_left B bounds first second).trans cost) hcode horacle hbitmap h)
      · intro middle hrun rr post t h
        obtain ⟨used, hused, hc, ho, hb⟩ := runBudget_after first source middle none hrun hfirst hcode horacle hbitmap
        have hsecond : steps (second, middle) ≤ n - used := by
          rw [steps_seq_run first second source middle hrun] at hsteps
          omega
        have smaller := seq_second_measure_lt first second source (evaluate (first, source))
        rw [StackSemEvaluateClock.fixClockEvaluate, hrun] at smaller
        normalize_step rr using (compCorrectWithinSteps second middle rr post t pointer bounds jump B K Kpos (n-used) hsecond
          ((leafCost_seq_right B bounds first second).trans cost) hc ho hb h)
    case ite cmp reg ri first second =>
      refine (by normalize_step result using (compCorrectIteWithinSteps cmp reg ri first second source result postSource target pointer bounds jump B K Kpos ?_ ?_ hypothesis))
      · intro x y hx hy hcmp rr post t h
        have hfirst : steps (first, source) ≤ n := by
          rw [steps_ite_true cmp reg ri first second source x y hx hy hcmp] at hsteps
          omega
        normalize_step rr using (compCorrectWithinSteps first source rr post t pointer bounds jump B K Kpos n hfirst
          ((leafCost_ite_left B bounds cmp reg ri first second).trans cost) hcode horacle hbitmap h)
      · intro x y hx hy hcmp rr post t h
        have hsecond : steps (second, source) ≤ n := by
          rw [steps_ite_false cmp reg ri first second source x y hx hy hcmp] at hsteps
          omega
        normalize_step rr using (compCorrectWithinSteps second source rr post t pointer bounds jump B K Kpos n hsecond
          ((leafCost_ite_right B bounds cmp reg ri first second).trans cost) hcode horacle hbitmap h)
    case loop body =>
      have hbodySteps : steps (body, source) ≤ n := (steps_loop_body_le body source).trans hsteps
      refine (by normalize_step result using (compCorrectLoopWithinSteps body source result postSource target pointer bounds jump B K Kpos ?_ ?_ hypothesis))
      · intro rr post t h
        normalize_step rr using (compCorrectWithinSteps body source rr post t pointer bounds jump B K Kpos n hbodySteps
          ((leafCost_loop B bounds body).trans cost) hcode horacle hbitmap h)
      · intro br middle hbody hcont hz rr post t h
        obtain ⟨used, hused, hc, ho, hb⟩ := runBudget_after body source middle br hbody hbodySteps hcode horacle hbitmap
        have hnext : steps (.loop body, decClock middle) ≤ n - used := by
          rw [steps_loop_run body source middle br hbody hcont hz] at hsteps
          omega
        have hp := runBudget_congr middle (decClock middle) rfl rfl rfl hc ho hb
        have smaller := loop_reentry_measure_lt body source (evaluate (body, source)) (by
          rw [StackSemEvaluateClock.fixClockEvaluate, hbody]; exact hz)
        rw [StackSemEvaluateClock.fixClockEvaluate, hbody] at smaller
        normalize_step rr using (compCorrectWithinSteps (.loop body) (decClock middle) rr post t pointer bounds jump B K Kpos (n-used) hnext cost hp.1 hp.2.1 hp.2.2 h)
    case jumpLower first second label =>
      refine (by normalize_step result using (compCorrectJumpLowerWithinSteps first second label source result postSource target pointer bounds jump B K Kpos ?_ hypothesis))
      intro left right prog hl hr hcmp hlookup hz rr post t h
      have smaller := callee_measure_lt prog (.jumpLower first second label) source hz
      have hcallee : steps (prog, decClock source) ≤ n := by
        rw [steps_jumpLower] at hsteps
        simp only [hl, hr, hcmp, if_true, StackSemControl.findCode, hlookup, hz, if_false] at hsteps
        omega
      have hp := runBudget_congr source (decClock source) rfl rfl rfl hcode horacle hbitmap
      normalize_step rr using (compCorrectWithinSteps prog (decClock source) rr post t pointer bounds jump B K Kpos n hcallee
        (hcode label prog hlookup) hp.1 hp.2.1 hp.2.2 h)
    case rawCall label =>
      refine (by normalize_step result using (compCorrectRawCallWithinSteps label source result postSource target pointer bounds jump B K Kpos ?_ hypothesis))
      intro frame body hlookup hz rr post t h
      have smaller := callee_measure_lt body (.rawCall label) source hz
      have hcallee : steps (body, decClock source) ≤ n := by
        rw [steps_rawCall] at hsteps
        simp only [hlookup, StackSemControl.destSeq, hz, if_false] at hsteps
        omega
      have hbody := (leafCost_seq_right B bounds frame body).trans (hcode label (.seq frame body) hlookup)
      have hp := runBudget_congr source (decClock source) rfl rfl rfl hcode horacle hbitmap
      normalize_step rr using (compCorrectWithinSteps body (decClock source) rr post t pointer bounds jump B K Kpos n hcallee
        hbody hp.1 hp.2.1 hp.2.2 h)
    case call ret dest handler =>
      refine (by normalize_step result using (compCorrectCallWithinSteps ret dest handler source result postSource target pointer bounds jump B K Kpos cost ?_ ?_ ?_ hypothesis))
      · cases ret with
        | none =>
          intro prog hfind hhandler hz rr post t h
          subst handler
          obtain ⟨label, hlookup⟩ := findCode_sptLookup hfind
          have smaller := callee_measure_lt prog (.call none dest none) source hz
          have hcallee : steps (prog, decClock source) ≤ n := by
            rw [steps_call_none] at hsteps
            simp only [hfind, hz, if_false] at hsteps
            omega
          have hp := runBudget_congr source (decClock source) rfl rfl rfl hcode horacle hbitmap
          normalize_step rr using (compCorrectWithinSteps prog (decClock source) rr post t pointer bounds jump B K Kpos n hcallee
            (hcode label prog hlookup) hp.1 hp.2.1 hp.2.2 h)
        | some entry =>
          rcases entry with ⟨body, link, l1, l2⟩
          intro prog hfind hz rr post t h
          obtain ⟨label, hlookup⟩ := findCode_sptLookup hfind
          let start := decClock (setVar link (.loc l1 l2) source)
          have hcallee : steps (prog, start) ≤ n := by
            apply le_trans ?_ hsteps
            dsimp only [start]
            rw [steps_call_some]
            simp only [hfind, hz, if_false]
            exact (Nat.le_add_right _ _).trans (Nat.le_add_left _ _)
          have hp := runBudget_congr source start rfl rfl rfl hcode horacle hbitmap
          have hnonzero : (setVar link (.loc l1 l2) source).clock ≠ 0 := by simpa [setVar] using hz
          have smaller := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) source) hnonzero
          have hpar : stackSemMeasure (.call (some (body, link, l1, l2)) dest handler) (setVar link (.loc l1 l2) source) =
              stackSemMeasure (.call (some (body, link, l1, l2)) dest handler) source := by simp [stackSemMeasure, setVar]
          rw [hpar] at smaller
          normalize_step rr using (compCorrectWithinSteps prog start rr post t pointer bounds jump B K Kpos n hcallee
            (hcode label prog hlookup) hp.1 hp.2.1 hp.2.2 h)
      · cases ret with
        | none => trivial
        | some entry =>
          rcases entry with ⟨body, link, l1, l2⟩
          intro prog middle hfind hz hrun rr post t h
          let start := decClock (setVar link (.loc l1 l2) source)
          have hfix := StackSemEvaluateClock.fixClockEvaluate prog start
          change evaluate (prog, start) = _ at hrun
          rw [hrun] at hfix
          have hsum : steps (prog, start) + steps (body, middle) ≤ n := by
            apply le_trans ?_ hsteps
            rw [steps_call_some]
            simp only [hfind, hz, if_false]
            rw [hrun, hfix]
            simp only [if_true]
            exact Nat.le_add_left _ _
          have hcallee : steps (prog, start) ≤ n := (Nat.le_add_right _ _).trans hsum
          have hp := runBudget_congr source start rfl rfl rfl hcode horacle hbitmap
          obtain ⟨used, hused, hc, ho, hb⟩ := runBudget_after prog start middle _ hrun hcallee hp.1 hp.2.1 hp.2.2
          have hnext : steps (body, middle) ≤ n - used := by omega
          have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler) source link l1 l2
            (evaluate (prog, start)) hz
          rw [StackSemEvaluateClock.fixClockEvaluate, hrun] at smaller
          normalize_step rr using (compCorrectWithinSteps body middle rr post t pointer bounds jump B K Kpos (n-used) hnext
            ((SteppedFlapjack.StackRemoveSteps.callLeafCostReturn B bounds body link l1 l2 dest handler).trans cost) hc ho hb h)
      · cases ret with
        | none => trivial
        | some entry =>
          rcases entry with ⟨body, link, l1, l2⟩
          cases handler with
          | none => trivial
          | some entry =>
            rcases entry with ⟨handlerBody, hl1, hl2⟩
            intro prog middle hfind hz hrun rr post t h
            let start := decClock (setVar link (.loc l1 l2) source)
            have hfix := StackSemEvaluateClock.fixClockEvaluate prog start
            change evaluate (prog, start) = _ at hrun
            rw [hrun] at hfix
            have hsum : steps (prog, start) + steps (handlerBody, middle) ≤ n := by
              apply le_trans ?_ hsteps
              rw [steps_call_some]
              simp only [hfind, hz, if_false]
              rw [hrun, hfix]
              simp only [if_true]
              exact Nat.le_add_left _ _
            have hcallee : steps (prog, start) ≤ n := (Nat.le_add_right _ _).trans hsum
            have hp := runBudget_congr source start rfl rfl rfl hcode horacle hbitmap
            obtain ⟨used, hused, hc, ho, hb⟩ := runBudget_after prog start middle _ hrun hcallee hp.1 hp.2.1 hp.2.2
            have hnext : steps (handlerBody, middle) ≤ n - used := by omega
            have smaller := call_continuation_measure_lt handlerBody
              (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2))) source link l1 l2
              (evaluate (prog, start)) hz
            rw [StackSemEvaluateClock.fixClockEvaluate, hrun] at smaller
            normalize_step rr using (compCorrectWithinSteps handlerBody middle rr post t pointer bounds jump B K Kpos (n-used) hnext
              ((SteppedFlapjack.StackRemoveSteps.callLeafCostHandler B bounds (some (body, link, l1, l2)) dest handlerBody hl1 hl2).trans cost) hc ho hb h)

termination_by stackSemMeasure program source

decreasing_by
  all_goals subst program
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, hrun] at smaller)
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate, hbody] at smaller)
  all_goals try (rw [hpar] at smaller)
  all_goals first
    | assumption
    | exact seq_first_measure_lt _ _ _
    | exact if_first_measure_lt _ _ _ _ _ _
    | exact if_second_measure_lt _ _ _ _ _ _
    | exact loop_body_measure_lt _ _
    | (have hh := StackSemEvaluateClock.evaluateClock _ _ _ _ hrun
       apply lexNat_of_clock_lt
       try dsimp only [start, decClock, setVar] at hh
       try simp only [decClock, setVar] at hh ⊢
       omega)
    | (apply lexNat_of_clock_lt
       try simp only [decClock, setVar]
       omega)

/-- A source step bound determines the finite code, oracle, and bitmap factors
needed to bound the compiled stack-removal run. -/
theorem compCorrectWithinStepsComputed
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool) (n : Nat)
    (hsteps : steps (program, source) ≤ n)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer program, {target with clock := clock + target.clock}) ≤
        computedRunCost bounds n program source * n := by
  let B := initialBitmapBudget n source
  let K := computedRunCost bounds n program source
  have hi := computedRunCost_bounds bounds n program source
  have hb : source.bitmaps.length + oracleBitmapBudget n source.compileOracle ≤ B := by rfl
  obtain ⟨clock, postTarget, run, relation, bound⟩ :=
    compCorrectWithinSteps program source result postSource target pointer bounds jump B K
      hi.2.1 n hsteps hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2 hb hypothesis
  refine ⟨clock, postTarget, run, ?_, ?_⟩
  · cases result with
    | none => exact relation
    | some returned => cases returned <;> exact relation
  · exact bound.trans (Nat.mul_le_mul_left K hsteps)

end SteppedFlapjack.StackRemoveSteps.CompCorrect
