import SteppedFlapjack.CrepToLoopSteps.ScalarLoop
import SteppedFlapjack.LoopLiveSteps.OptimiseShape
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]
/-- Any property preserved by shrinking is preserved by a successful fixed point. -/
theorem scalarFixedpoint_preserves {body : HolLoopProg width} (property : HolLoopProg width → Prop)
    (shape : ∀ lt live, property (shrinkHOL lt body live).1) :
    ∀ lt liveIn l1 l2 out live, fixedpointHOL lt liveIn l1 l2 body = some (out,live) → property out := by
  have key : ∀ fuel lt liveIn l1 l2 out live,
      sptSize liveIn - sptSize l1 < fuel →
      fixedpointHOL lt liveIn l1 l2 body = some (out,live) → property out := by
    intro fuel
    induction fuel with
    | zero => intro lt li l1 l2 out live enough; omega
    | succ fuel ih =>
      intro lt li l1 l2 out live enough eq
      rw [fixedpointHOL] at eq
      rcases h : shrinkHOL ((sptInter li l1,l2)::lt) body l2 with ⟨b,l0⟩
      simp only [h] at eq
      split at eq
      · cases eq
        simpa [h] using shape ((sptInter li l1,l2)::lt) l2
      · split at eq
        · simp at eq
        · rename_i stable progress
          apply ih lt li (sptInter li l0) l2 out live ?_ eq
          have bound := sptSize_inter_le li l0
          omega
  intro lt li l1 l2 out live eq
  exact key (sptSize li + 1) lt li l1 l2 out live (by omega) eq
/-- Liveness shrinking preserves the recursive scalar Loop grammar. -/
theorem scalarLoop_shrink {p : HolLoopProg width} (shape : ScalarLoop p) :
    ∀ lt live, ScalarLoop (shrinkHOL lt p live).1 := by
  induction shape with
  | branch h => intro lt live; exact .branch (shrink_branch h lt live)
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL]
    rcases h : shrinkHOL lt b live with ⟨bb,l⟩
    rcases hh : shrinkHOL lt a l with ⟨aa,ll⟩
    simp only
    exact .seq (by simpa [hh] using iha lt l) (by simpa [h] using ihb lt live)
  | @ite cmp r ri ls a b ha hb iha ihb =>
    intro lt live
    cases ri <;> simp only [shrinkHOL]
    all_goals rcases h : shrinkHOL lt a (sptInter live ls) with ⟨aa,la⟩
    all_goals rcases hh : shrinkHOL lt b (sptInter live ls) with ⟨bb,lb⟩
    all_goals simp only
    all_goals exact .ite _ _ _ _ (by simpa [h] using iha lt (sptInter live ls)) (by simpa [hh] using ihb lt (sptInter live ls))
  | @loop li lo body hb ih =>
    intro lt live
    simp only [shrinkHOL]
    generalize heq : fixedpointHOL lt li .ln (sptUnion li (sptInter lo live)) body = outcome
    cases outcome with
    | none =>
      rcases h : shrinkHOL ((li,sptInter lo live)::lt) body (sptUnion li (sptInter lo live)) with ⟨b,l⟩
      simp only
      exact .loop _ _ (by simpa [h] using ih ((li,sptInter lo live)::lt) (sptUnion li (sptInter lo live)))
    | some pair =>
      rcases pair with ⟨b,l⟩
      simp only
      exact .loop _ _ (scalarFixedpoint_preserves ScalarLoop ih lt li .ln _ b l heq)
/-- The Loop call pass leaves recursive scalar programs unchanged. -/
theorem scalarLoop_call {p : HolLoopProg width} (shape : ScalarLoop p) :
    ∀ env, (loopCallCompHOL env p).1 = p := by
  induction shape with
  | branch h => exact loopCall_branch h
  | @seq a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL]
    rw [iha env,ihb (loopCallCompHOL env a).2]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL,iha env,ihb env]
  | @loop li lo body h ih =>
    intro env
    simp only [loopCallCompHOL,ih]

/-- Marking preserves recursive scalar Loop programs. -/
theorem scalarLoop_mark {p : HolLoopProg width} (shape : ScalarLoop p) :
    ScalarLoop (markAllHOL p).1 ∧ ((markAllHOL p).2 = true → LoopBranch (markAllHOL p).1) := by
  induction shape with
  | branch h =>
    have hh := markAll_branch h
    exact ⟨.branch hh.1,fun _ => hh.1⟩
  | @loop li lo body h ih =>
    simp only [markAllHOL]
    exact ⟨.loop _ _ ih.1,by simp⟩
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h1 : (markAllHOL a).2 <;> cases h2 : (markAllHOL b).2 <;>
      simp only [h1,h2,Bool.false_and,Bool.true_and,if_true] at *
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · have branch := LoopBranch.seq (iha.2 True.intro) (ihb.2 True.intro)
      exact ⟨.branch (.mark branch),fun _ => .mark branch⟩
  | @ite cmp r ri ls a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h1 : (markAllHOL a).2 <;> cases h2 : (markAllHOL b).2 <;>
      simp only [h1,h2,Bool.false_and,Bool.true_and,if_true] at *
    · exact ⟨.ite _ _ _ _ iha.1 ihb.1,by simp⟩
    · exact ⟨.ite _ _ _ _ iha.1 ihb.1,by simp⟩
    · exact ⟨.ite _ _ _ _ iha.1 ihb.1,by simp⟩
    · have branch := LoopBranch.ite cmp r ri ls (iha.2 True.intro) (ihb.2 True.intro)
      exact ⟨.branch (.mark branch),fun _ => .mark branch⟩

/-- The complete Loop optimizer retains recursive scalar shape. -/
theorem scalarLoop_optimise {p : HolLoopProg width} (shape : ScalarLoop p) :
    ScalarLoop (optimiseHOL p) := by
  simp only [optimiseHOL,scalarLoop_call shape .ln,compHOL]
  exact (scalarLoop_mark (scalarLoop_shrink shape [] .ln)).1

end SteppedFlapjack.CrepToLoopSteps
