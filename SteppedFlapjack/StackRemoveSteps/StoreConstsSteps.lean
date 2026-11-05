import SteppedFlapjack.StackRemoveSteps.CopyLoopSteps
/-! Step overhead of the constant-store expansion. The remaining cost is the
actual bitmap-copy run reached after the three-instruction prefix. -/

namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove Flapjack.StackSemEvaluate
open Flapjack.StackSemControl Flapjack.Compiler.Encoders.Asm SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}
theorem steps_three_prefix (i1 i2 i3 i4 i5 : HolInst width) (body : HolProg width)
    (s prepared : StackSemStateFiniteExact width C F)
    (pre : evaluate (listSeqHOL [.inst i1, .inst i2, .inst i3], s) = (none, prepared)) :
    steps (listSeqHOL [.inst i1, .inst i2, .inst i3, body, .inst i4, .inst i5], s) ≤
      10 + steps (body, prepared) := by
  rcases h1 : evaluate ((.inst i1 : HolProg width), s) with ⟨r1, s1⟩
  rcases h2 : evaluate ((.inst i2 : HolProg width), s1) with ⟨r2, s2⟩
  rw [show listSeqHOL [.inst i1, .inst i2, .inst i3] =
    (.seq (.inst i1) (.seq (.inst i2) (.inst i3)) : HolProg width) from rfl,
    evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, h1] at pre
  cases r1 with
  | some x => cases pre
  | none =>
    dsimp only at pre
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, h2] at pre
    cases r2 with
    | some x => cases pre
    | none =>
      dsimp only at pre
      simp only [listSeqHOL]
      rw [steps_seq_run _ _ _ _ h1, steps_seq_run _ _ _ _ h2,
        steps_seq_run _ _ _ _ pre]
      simp only [steps_inst]
      rw [steps_seq]
      rcases hh : fixClock prepared (evaluate (body, prepared)) with ⟨res, post⟩
      cases res with
      | none =>
        simp only
        have tail : steps ((.seq (.inst i4) (.inst i5) : HolProg width), post) ≤ 3 := by
          exact steps_seq_le (ba := 1) (bb := 1)
            (fun t => le_of_eq (steps_inst i4 t)) (fun t => le_of_eq (steps_inst i5 t))
        omega
      | some value => simp only; omega
theorem steps_comp_storeConsts_of_prefix (jump : Bool) (bounds : BitVec width × BitVec width)
    (pointer temporary bitmap : Nat) (stub : Option Nat)
    (s prepared : StackSemStateFiniteExact width C F)
    (pre : evaluate (listSeqHOL [.inst (.mem .load bitmap (.addr (pointer + 1) (storeOffset .bitmapBase))),
      addInst bitmap 1, leftShiftInst bitmap (wordShiftAmount width)], s) = (none, prepared)) :
    steps (comp jump bounds pointer (.storeConsts temporary bitmap stub), s) ≤
      10 + steps (copyLoop temporary bitmap, prepared) := by
  simpa only [comp, addInst, leftShiftInst, moveInst, moveHOL] using
    steps_three_prefix (.mem .load bitmap (.addr (pointer + 1) (storeOffset .bitmapBase)))
      _ _ _ _ (copyLoop temporary bitmap) s prepared pre

end SteppedFlapjack.StackRemoveSteps
