import SteppedFlapjack.CrepToLoopSteps.ScalarLoopWeight
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopLive
import SteppedFlapjack.LoopLiveSteps.ClockBound
import SteppedFlapjack.LoopSteps.ClockConsumption
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- Recursive scalar Loop executions consume at most two clock units per visit. -/
theorem scalarLoop_consumed {p : HolLoopProg width} (shape : ScalarLoop p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) : s.clock - post.clock ≤ 2 * steps p s := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_clock_consumed (branch_branched h) s post result run
    omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstBound := iha s middle out first
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have secondBound := ihb middle post result run
      have secondClock := evaluate_clock b middle result post run
      omega
    | some x =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      omega
  | @ite cmp reg ri live a b ha hb iha ihb =>
    rw [steps_ite]
    simp only [evaluate] at run
    rcases hx : sptLookup reg s.locals with _ | (x | ⟨_,_⟩) <;>
      rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only [hx,hy] at run ⊢ <;>
      try (cases run; simp)
    by_cases hcmp : wordCmpHOL cmp x y = true
    · simp only [hcmp,if_true] at run ⊢
      rcases branch : evaluate a s with ⟨br,middle⟩
      have hb := iha s middle br branch
      have hc := cutRes_clock_consumed live br middle
      have he := evaluate_clock a s br middle branch
      rw [branch] at run
      have ht : (cutRes live (br,middle)).2.clock = post.clock := by rw [run]
      rw [ht] at hc
      omega
    · simp only [hcmp,Bool.false_eq_true,if_false] at run ⊢
      rcases branch : evaluate b s with ⟨br,middle⟩
      have hb := ihb s middle br branch
      have hc := cutRes_clock_consumed live br middle
      have he := evaluate_clock b s br middle branch
      rw [branch] at run
      have ht : (cutRes live (br,middle)).2.clock = post.clock := by rw [run]
      rw [ht] at hc
      omega
  | @loop live exits body bodyShape bodyIH =>
    induction hs : s.clock using Nat.strongRecOn generalizing s post result with
    | _ clock ih =>
      rcases cut : cutRes live (none,s) with ⟨cutResult,entry⟩
      have cutBound := cutRes_clock_consumed live none s
      rw [cut] at cutBound
      simp only at cutBound
      cases cutResult with
      | some r =>
        have execution := run
        rw [evaluate,cut] at execution
        simp only [Prod.mk.injEq] at execution
        obtain ⟨_,rfl⟩ := execution
        rw [steps_loop,cut]
        simp only at cutBound ⊢
        omega
      | none =>
        rcases bodyRun : evaluate body entry with ⟨bodyResult,middle⟩
        have entryClock := cutRes_none_clock cut
        have bodyClock := evaluate_clock body entry bodyResult middle bodyRun
        have bodyBound := bodyIH entry middle bodyResult bodyRun
        have execution := run
        rw [evaluate,cut] at execution
        simp only at execution
        rw [fix_clock_evaluate,bodyRun] at execution
        rw [steps_loop,cut]
        simp only
        rw [bodyRun]
        by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
        · have recurRun : evaluate (.loop live body exits) middle = (result,post) := by
            rcases continuing with h | h <;> rw [h] at execution <;> exact execution
          have smaller : middle.clock < s.clock := by omega
          have recur := ih middle.clock (by simpa [hs] using smaller) middle post result recurRun rfl
          have finalClock := evaluate_clock (.loop live body exits) middle result post recurRun
          rcases continuing with h | h <;> rw [h] <;> simp only <;> omega
        · have hnone : bodyResult ≠ none := fun h => continuing (Or.inl h)
          have hcont : bodyResult ≠ some (.continue 0) := fun h => continuing (Or.inr h)
          cases bodyResult with
          | none => exact (hnone rfl).elim
          | some r =>
            cases r <;> try (simp only at execution ⊢; cases execution; omega)
            case «break» label =>
              cases label with
              | zero =>
                simp only at execution ⊢
                have exitBound := cutRes_clock_consumed exits none middle
                rw [execution] at exitBound
                simp only at exitBound
                omega
              | succ n => simp only at execution ⊢; cases execution; omega
private theorem terminal_arith (start entry finish cost visits : Nat)
    (entryLt : entry < start) (finishLe : finish ≤ entry)
    (bound : visits ≤ cost * (entry - finish + 1)) :
    1 + visits ≤ (1 + cost) * (start - finish + 1) := by
  have budget : entry - finish + 1 ≤ start - finish + 1 := by omega
  have scaled := Nat.mul_le_mul_left cost budget
  have positive : 1 ≤ start - finish + 1 := by omega
  nlinarith

/-- A loop visit bound lifts a clock-consumption bound for its body. -/
private theorem nested_loop_bound (live exits : NumSet) (body : HolLoopProg width) (cost : Nat)
    (bodyBound : ∀ (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width)),
      evaluate body s = (result,post) →
      steps body s ≤ cost * (s.clock - post.clock + 1))
    (s final : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate (.loop live body exits) s = (result,final)) :
    steps (.loop live body exits) s ≤ (1 + cost) * (s.clock - final.clock + 1) := by
  induction hs : s.clock using Nat.strongRecOn generalizing s final result with
  | _ clock ih =>
    rcases cut : cutRes live (none,s) with ⟨cutResult,entry⟩
    cases cutResult with
    | some r =>
      rw [steps_loop,cut]
      simp only
      have budget : 1 ≤ clock - final.clock + 1 := by omega
      nlinarith
    | none =>
      rcases bodyRun : evaluate body entry with ⟨bodyResult,middle⟩
      have entryClock := cutRes_none_clock cut
      have bodyClock := evaluate_clock body entry bodyResult middle bodyRun
      have bodyVisits := bodyBound entry middle bodyResult bodyRun
      have execution := run
      rw [evaluate,cut] at execution
      simp only at execution
      rw [fix_clock_evaluate,bodyRun] at execution
      simp only [← hs] at *
      rw [steps_loop,cut]
      simp only
      rw [bodyRun]
      by_cases continuing : bodyResult = none ∨ bodyResult = some (.continue 0)
      · have recurRun : evaluate (.loop live body exits) middle = (result,final) := by
          rcases continuing with h | h <;> rw [h] at execution <;> exact execution
        have smaller : middle.clock < s.clock := by omega
        have recur := ih middle.clock smaller middle final result recurRun rfl
        have finalClock := evaluate_clock (.loop live body exits) middle result final recurRun
        have budget : entry.clock - middle.clock + 1 + (middle.clock - final.clock + 1) ≤
            s.clock - final.clock + 1 := by omega
        have scaled := Nat.mul_le_mul_left (1 + cost) budget
        rcases continuing with h | h <;> rw [h] <;> simp only <;> nlinarith
      · have hnone : bodyResult ≠ none := fun h => continuing (Or.inl h)
        have hcont : bodyResult ≠ some (.continue 0) := fun h => continuing (Or.inr h)
        cases bodyResult with
        | none => exact (hnone rfl).elim
        | some r =>
          cases r <;> try (simp only at execution ⊢; cases execution; exact terminal_arith _ _ _ _ _ entryClock bodyClock bodyVisits)
          case «continue» label =>
            cases label with
            | zero => exact (hcont rfl).elim
            | succ n => simp only at execution ⊢; cases execution; exact terminal_arith _ _ _ _ _ entryClock bodyClock bodyVisits
          case «break» label =>
            cases label with
            | zero =>
              simp only at execution ⊢
              have exitClock := cutRes_clock_le exits (none,middle)
              rw [execution] at exitClock
              simp only at exitClock
              have budget : entry.clock - middle.clock + 1 ≤ s.clock - final.clock + 1 := by omega
              have scaled := Nat.mul_le_mul_left (1 + cost) budget
              nlinarith
            | succ n => simp only at execution ⊢; cases execution; exact terminal_arith _ _ _ _ _ entryClock bodyClock bodyVisits

/-- Visits are bounded by control-node weight and the clock actually consumed, even for
nested loops and branches. The bound is independent of unused input clock. -/
theorem scalarLoop_control_consumption_bound {p : HolLoopProg width} (shape : ScalarLoop p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) :
    steps p s ≤ loopVisitWeight p * (s.clock - post.clock + 1) := by
  induction shape generalizing s post result with
  | branch h =>
    have bound := branchedProgram_structural_bound (branch_branched h) s
    rw [branch_visitWeight h]
    nlinarith
  | @loop live exits body h ih =>
    have bound := nested_loop_bound live exits body (loopVisitWeight body) ih s post result run
    have size : 1 + loopVisitWeight body ≤ loopVisitWeight (.loop live body exits : HolLoopProg width) := by simp [loopVisitWeight]
    exact bound.trans (Nat.mul_le_mul_right _ size)
  | @seq a b ha hb iha ihb =>
    have size : 1 + loopVisitWeight a + loopVisitWeight b ≤ loopVisitWeight (.seq a b : HolLoopProg width) := by simp [loopVisitWeight]
    rw [steps_seq,evaluate_seq] at *
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have firstBound := iha s middle out first
    have firstClock := evaluate_clock a s out middle first
    cases out with
    | none =>
      simp only at run ⊢
      have secondBound := ihb middle post result run
      have secondClock := evaluate_clock b middle result post run
      have budget1 : s.clock - middle.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have budget2 : middle.clock - post.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have scaled1 := Nat.mul_le_mul_left (loopVisitWeight a) budget1
      have scaled2 := Nat.mul_le_mul_left (loopVisitWeight b) budget2
      nlinarith
    | some x =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      simp only
      nlinarith
  | @ite cmp reg ri live a b ha hb iha ihb =>
    have sizeA : 1 + loopVisitWeight a ≤ loopVisitWeight (.ite cmp reg ri a b live : HolLoopProg width) := by simp [loopVisitWeight]
    have sizeB : 1 + loopVisitWeight b ≤ loopVisitWeight (.ite cmp reg ri a b live : HolLoopProg width) := by simp [loopVisitWeight]
    rw [steps_ite]
    simp only [evaluate] at run
    rcases hx : sptLookup reg s.locals with _ | (x | ⟨_,_⟩) <;>
      rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only [hx,hy] at run ⊢ <;>
      try (cases run; simp; nlinarith)
    by_cases hcmp : wordCmpHOL cmp x y = true
    · simp only [hcmp,if_true] at run ⊢
      rcases branch : evaluate a s with ⟨br,middle⟩
      have visits := iha s middle br branch
      have hc := cutRes_clock_le live (br,middle)
      have he := evaluate_clock a s br middle branch
      rw [branch] at run
      have ht : (cutRes live (br,middle)).2.clock = post.clock := by rw [run]
      rw [ht] at hc
      simp only at hc
      have budget : s.clock - middle.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have scaled := Nat.mul_le_mul_left (loopVisitWeight a) budget
      nlinarith
    · simp only [hcmp,Bool.false_eq_true,if_false] at run ⊢
      rcases branch : evaluate b s with ⟨br,middle⟩
      have visits := ihb s middle br branch
      have hc := cutRes_clock_le live (br,middle)
      have he := evaluate_clock b s br middle branch
      rw [branch] at run
      have ht : (cutRes live (br,middle)).2.clock = post.clock := by rw [run]
      rw [ht] at hc
      simp only at hc
      have budget : s.clock - middle.clock + 1 ≤ s.clock - post.clock + 1 := by omega
      have scaled := Nat.mul_le_mul_left (loopVisitWeight b) budget
      nlinarith

/-- The control bound implies the coarser code-size bound. -/
theorem scalarLoop_consumption_bound {p : HolLoopProg width} (shape : ScalarLoop p)
    (s post : LoopSemStateFiniteExact width F) (result : Option (LoopResultExact width))
    (run : evaluate p s = (result,post)) :
    steps p s ≤ sizeOf p * (s.clock - post.clock + 1) := by
  exact (scalarLoop_control_consumption_bound shape s post result run).trans
    (Nat.mul_le_mul_right _ (scalarLoop_visitWeight_le_size shape))

/-- The actual optimizer preserves a completed recursive scalar Loop run and
its visits are bounded by optimized code size and original visits. -/
theorem scalarLoop_optimise_source_steps {p : HolLoopProg 64} (shape : ScalarLoop p)
    (s post : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (run : evaluate p s = (result,post)) (complete : CompleteLoopResult result) :
    evaluate (optimiseHOL p) s = (result,post) ∧
    ScalarLoop (optimiseHOL p) ∧
    steps (optimiseHOL p) s ≤ sizeOf (optimiseHOL p) * (2 * steps p s + 1) := by
  have optRun : evaluate (optimiseHOL p) s = (result,post) := by
    apply optimise_correct p s result post
    refine ⟨run,?_,?_,?_,?_⟩ <;> cases complete <;> simp_all
  have optShape := scalarLoop_optimise shape
  have optBound := scalarLoop_consumption_bound optShape s post result optRun
  have used := scalarLoop_consumed shape s post result run
  exact ⟨optRun,optShape,optBound.trans (Nat.mul_le_mul_left _ (by omega))⟩

end SteppedFlapjack.CrepToLoopSteps
