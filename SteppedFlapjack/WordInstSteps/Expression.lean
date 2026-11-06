import SteppedFlapjack.WordSteps.Defs
import SteppedFlapjack.WordToStackSteps.LoopZeroClock
import Flapjack.Compiler.Backend.WordInst.Proofs.InstSelect
namespace SteppedFlapjack.WordInstSteps
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordInst Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordToStackSteps

/-- Straight-line instructions emitted by expression selection. -/
inductive Straight {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | inst (i) : Straight (.inst i)
  | move (priority moves) : Straight (.move priority moves)
  | get (dst name) : Straight (.get dst name)
  | setVar (name src) : Straight (.set name (.var src))
  | opCurrHeap (op dst src) : Straight (.opCurrHeap op dst src)
  | skip : Straight .skip
  | seq {a b} : Straight a → Straight b → Straight (.seq a b)

/-- Expression instruction selection generates only Word-to-Stack blocks. -/
theorem selectExp_block {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (dst temp : Nat) (e : WordLangExpHOL (BitVec width)) : LoopBlock (instSelectExp ac dst temp e) := by
  cases e with
  | const w => simpa only [instSelectExp] using (LoopBlock.inst (.const dst w) : LoopBlock (.inst (.const dst w)))
  | var v => simpa only [instSelectExp] using (LoopBlock.move 0 [(dst,v)] : LoopBlock (.move 0 [(dst,v)] : WordLangProgHOL (BitVec width)))
  | lookup n => simpa only [instSelectExp] using (LoopBlock.get dst n : LoopBlock (.get dst n : WordLangProgHOL (BitVec width)))
  | load address =>
    rw [instSelectExp.eq_def]
    simp only
    split
    · split <;> exact .seq (selectExp_block ac _ _ _) (.inst _)
    · exact .seq (selectExp_block ac _ _ _) (.inst _)
  | op op args =>
    cases args with
    | nil => simpa only [instSelectExp] using (LoopBlock.skip : LoopBlock (.skip : WordLangProgHOL (BitVec width)))
    | cons x rest =>
      cases rest with
      | nil => simpa only [instSelectExp] using (LoopBlock.skip : LoopBlock (.skip : WordLangProgHOL (BitVec width)))
      | cons y rest =>
        cases rest with
        | cons z rest => simpa only [instSelectExp] using (LoopBlock.skip : LoopBlock (.skip : WordLangProgHOL (BitVec width)))
        | nil =>
          rw [instSelectExp.eq_def]
          simp only
          split
          · exact .seq (selectExp_block ac _ _ _) (.opCurrHeap _ _ _)
          · split
            · exact .seq (selectExp_block ac _ _ _) (.opCurrHeap _ _ _)
            · split
              · split
                · exact .seq (selectExp_block ac _ _ _) (.inst _)
                · split
                  · exact .seq (selectExp_block ac _ _ _) (.inst _)
                  · exact .seq (selectExp_block ac _ _ _) (.seq (.inst _) (.inst _))
              · exact .seq (selectExp_block ac _ _ _) (.seq (selectExp_block ac _ _ _) (.inst _))
  | shift op a b =>
    rw [instSelectExp.eq_def]
    simp only
    split
    · split
      · split
        · exact .seq (selectExp_block ac _ _ _) (.move _ _)
        · exact .seq (selectExp_block ac _ _ _) (.inst _)
      · exact .inst _
    · exact .seq (selectExp_block ac _ _ _) (.seq (selectExp_block ac _ _ _) (.inst _))
termination_by sizeOf e
decreasing_by
  all_goals (try subst_vars)
  all_goals simp_wf
  all_goals omega

/-- Expression instruction selection is straight-line. -/
theorem selectExp_straight {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (dst temp : Nat) (e : WordLangExpHOL (BitVec width)) : Straight (instSelectExp ac dst temp e) := by
  cases e with
  | const w => simpa only [instSelectExp] using (Straight.inst (.const dst w) : Straight (.inst (.const dst w)))
  | var v => simpa only [instSelectExp] using (Straight.move 0 [(dst,v)] : Straight (.move 0 [(dst,v)] : WordLangProgHOL (BitVec width)))
  | lookup n => simpa only [instSelectExp] using (Straight.get dst n : Straight (.get dst n : WordLangProgHOL (BitVec width)))
  | load address =>
    rw [instSelectExp.eq_def]
    simp only
    split
    · split <;> exact .seq (selectExp_straight ac _ _ _) (.inst _)
    · exact .seq (selectExp_straight ac _ _ _) (.inst _)
  | op op args =>
    cases args with
    | nil => simpa only [instSelectExp] using (Straight.skip : Straight (.skip : WordLangProgHOL (BitVec width)))
    | cons x rest =>
      cases rest with
      | nil => simpa only [instSelectExp] using (Straight.skip : Straight (.skip : WordLangProgHOL (BitVec width)))
      | cons y rest =>
        cases rest with
        | cons z rest => simpa only [instSelectExp] using (Straight.skip : Straight (.skip : WordLangProgHOL (BitVec width)))
        | nil =>
          rw [instSelectExp.eq_def]
          simp only
          split
          · exact .seq (selectExp_straight ac _ _ _) (.opCurrHeap _ _ _)
          · split
            · exact .seq (selectExp_straight ac _ _ _) (.opCurrHeap _ _ _)
            · split
              · split
                · exact .seq (selectExp_straight ac _ _ _) (.inst _)
                · split
                  · exact .seq (selectExp_straight ac _ _ _) (.inst _)
                  · exact .seq (selectExp_straight ac _ _ _) (.seq (.inst _) (.inst _))
              · exact .seq (selectExp_straight ac _ _ _) (.seq (selectExp_straight ac _ _ _) (.inst _))
  | shift op a b =>
    rw [instSelectExp.eq_def]
    simp only
    split
    · split
      · split
        · exact .seq (selectExp_straight ac _ _ _) (.move _ _)
        · exact .seq (selectExp_straight ac _ _ _) (.inst _)
      · exact .inst _
    · exact .seq (selectExp_straight ac _ _ _) (.seq (selectExp_straight ac _ _ _) (.inst _))
termination_by sizeOf e
decreasing_by
  all_goals (try subst_vars)
  all_goals simp_wf
  all_goals omega


/-- Selecting a memory store emits a straight-line address computation and
one store instruction. -/
theorem selectStore_straight {width : Nat} [NeZero width] (ac : AsmConfigExact width)
    (temp src : Nat) (e : WordLangExpHOL (BitVec width)) :
    Straight (instSelect ac temp (.store e src)) := by
  simp only [instSelect]
  split
  · split <;> exact .seq (selectExp_straight ac _ _ _) (.inst _)
  · exact .seq (selectExp_straight ac _ _ _) (.inst _)

/-- Straight-line selected code is in the proved Word-to-Stack fragment. -/
theorem straight_block {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (shape : Straight p) : LoopBlock p := by
  induction shape with
  | inst i => exact .inst _
  | move priority moves => exact .move _ _
  | get dst name => exact .get _ _
  | setVar name src => exact .set _ _
  | opCurrHeap op dst src => exact .opCurrHeap _ _ _
  | skip => exact .skip
  | seq ha hb iha ihb => exact .seq iha ihb

/-- Any straight-line generated fragment uses at most its syntax size in
actual Word evaluator visits, including early exits. -/
theorem straight_steps_bound {width : Nat} [NeZero width] {C F : Type}
    {p : WordLangProgHOL (BitVec width)} (shape : Straight p)
    (s : WordSemStateFiniteExact width C F) : WordSteps.steps p s ≤ sizeOf p := by
  induction shape generalizing s with
  | inst i => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | move priority moves => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | get dst name => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | setVar name src => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | opCurrHeap op dst src => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf; omega
  | skip => rw [WordSteps.steps_leaf _ _ rfl]; simp_wf
  | @seq a b ha hb iha ihb =>
    rw [WordSteps.steps_seq]
    have hfirst := iha s
    rcases evaluate a s with ⟨res,t⟩
    cases res with
    | none => have hsecond := ihb t; simp_wf; omega
    | some r => simp_wf; omega

/-- Expression code is flat and never dynamically installs code. -/
theorem straight_flat_noInstall {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (shape : Straight p) :
    flatExpConventions p = true ∧ noInstallSubprogsHOL p = true := by
  induction shape with
  | inst i => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | move priority moves => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | get dst name => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | setVar name src => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | opCurrHeap op dst src => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | skip => simp [flatExpConventions,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | @seq a b ha hb iha ihb =>
    simp only [noInstallSubprogsHOL] at iha ihb ⊢
    simp only [flatExpConventions,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨⟨iha.1,ihb.1⟩,iha.2,ihb.2⟩

end SteppedFlapjack.WordInstSteps
