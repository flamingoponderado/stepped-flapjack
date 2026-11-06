import SteppedFlapjack.LoopLiveSteps.ShrinkBranch

/-! The actual Loop optimizer preserves the supported source shape. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

/-- A loop-free branch is marked as a branch by the actual marking pass. -/
theorem markAll_branch {p : HolLoopProg width} (shape : LoopBranch p) :
    LoopBranch (markAllHOL p).1 ∧ (markAllHOL p).2 = true := by
  induction shape with
  | skip => exact ⟨.mark .skip,rfl⟩
  | tick => exact ⟨.mark .tick,rfl⟩
  | assign v e => exact ⟨.mark (.assign v e),rfl⟩
  | store e v => exact ⟨.mark (.store e v),rfl⟩
  | setGlobal v e => exact ⟨.mark (.setGlobal v e),rfl⟩
  | ret vs => exact ⟨.mark (.ret vs),rfl⟩
  | «break» n => exact ⟨.mark (.break n),rfl⟩
  | «continue» n => exact ⟨.mark (.continue n),rfl⟩
  | mark h ih => simpa only [markAllHOL] using ih
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL,iha.2,ihb.2,Bool.true_and,if_true]
    exact ⟨.mark (.seq iha.1 ihb.1),True.intro⟩
  | @ite cmp r ri ls a b ha hb iha ihb =>
    simp only [markAllHOL,iha.2,ihb.2,Bool.true_and,if_true]
    exact ⟨.mark (.ite _ _ _ _ iha.1 ihb.1),True.intro⟩

/-- If the marking pass reports a sequence as wholly markable, it is still a
loop-free branch; otherwise it remains a sequence of supported loops. -/
theorem markAll_sequence {p : HolLoopProg width} (shape : LoopSequenceSource p) :
    LoopSequenceSource (markAllHOL p).1 ∧ ((markAllHOL p).2 = true → LoopBranch (markAllHOL p).1) := by
  induction shape with
  | branch h =>
    have hh := markAll_branch h
    exact ⟨.branch hh.1,fun _ => hh.1⟩
  | loop live exits h =>
    simp only [markAllHOL]
    exact ⟨.loop _ _ (markAll_branch h).1,by simp⟩
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL]
    cases h1 : (markAllHOL a).2 <;> cases h2 : (markAllHOL b).2 <;>
      simp only [h1,h2,Bool.false_and,Bool.true_and,if_true] at *
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · exact ⟨.seq iha.1 ihb.1,by simp⟩
    · have branch := LoopBranch.seq (iha.2 True.intro) (ihb.2 True.intro)
      exact ⟨.branch (.mark branch),fun _ => .mark branch⟩

/-- The complete actual Loop optimizer retains the nonnested-loop fragment. -/
theorem optimise_sequence {p : HolLoopProg width} (shape : LoopSequenceSource p) :
    LoopSequenceSource (optimiseHOL p) := by
  simp only [optimiseHOL,loopCall_sequence shape .ln,compHOL]
  exact (markAll_sequence (shrink_sequence shape [] .ln)).1

end SteppedFlapjack.LoopLiveSteps
