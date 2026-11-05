import SteppedFlapjack.LoopSteps.DirectLeaf
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Seq

/-! Quantitative Loop-to-Word simulation for sequences. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.LoopToWord.CompileCorrect

/-- The original semantic result plus a non-increasing evaluator-node count. -/
def BoundPropertyAt {width : Nat} [NeZero width] (C : Type) {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) : Prop :=
  ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
    (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
    LoopSemStateFiniteExact.evaluate p s = (res,s1) ∧ res ≠ some .error ∧
      loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
      sptLookup 0 t.locals = some retv ∧ goodDimindex width ∧ ¬ wordSemIsWordLoc retv = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) →
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p l).1 t = (res1,t1) ∧
      t1.ffi = s1.ffi ∧ resultCase ctxt retv t res s1 res1 t1 ∧
      WordSteps.steps (LoopToWord.compHOL ctxt p l).1 t ≤ LoopSteps.steps p s

/-- Quantitative sequential composition, preserving all original result cases. -/
theorem boundedSeq {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    ((∀ res s1, (res, s1) = LoopSemStateFiniteExact.evaluate c1 s ∧ res = none →
        BoundPropertyAt C c2 s1) ∧ BoundPropertyAt C c1 s) →
      BoundPropertyAt C (.seq c1 c2) s := by
  rintro ⟨hSecond, hFirst⟩ res sFinal t ctxt retv l
      ⟨hSourceSeq, hNonError, hState, hLocals, hRetv, hDim, hWord, hAcc⟩
  have hAccFirst : ∀ k, sptMem k (accVarsHOL c1 .ln) → sptMem k ctxt := by
    intro k hk
    have hSplit : sptMem k (accVarsHOL c1 (accVarsHOL c2 .ln)) ↔
        sptMem k (accVarsHOL c1 .ln) ∨ sptMem k (accVarsHOL c2 .ln) := by
      change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    exact hAcc k (by simpa only [accVarsHOL] using hSplit.mpr (Or.inl hk))
  have hAccSecond : ∀ k, sptMem k (accVarsHOL c2 .ln) → sptMem k ctxt := by
    intro k hk
    have hSplit : sptMem k (accVarsHOL c1 (accVarsHOL c2 .ln)) ↔
        sptMem k (accVarsHOL c1 .ln) ∨ sptMem k (accVarsHOL c2 .ln) := by
      change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    exact hAcc k (by simpa only [accVarsHOL] using hSplit.mpr (Or.inr hk))
  have hPropagate (firstResult : LoopSemStateFiniteExact.LoopResultExact width)
      (hFirstNe : some firstResult ≠ some .error)
      (hFirstEval : LoopSemStateFiniteExact.evaluate c1 s = (some firstResult, sFinal)) :
      ∃ t1 res1,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.seq c1 c2) l).1 t =
          (res1, t1) ∧ t1.ffi = sFinal.ffi ∧
            resultCase ctxt retv t (some firstResult) sFinal res1 t1 ∧
          WordSteps.steps (LoopToWord.compHOL ctxt (.seq c1 c2) l).1 t ≤ LoopSteps.steps (.seq c1 c2) s := by
    have hFirstCase := hFirst (some firstResult) sFinal t ctxt retv l
      ⟨hFirstEval, hFirstNe, hState, hLocals, hRetv, hDim, hWord, hAccFirst⟩
    rcases hFirstCase with ⟨t1, res1, hTargetFirst, hFfiFirst, hResultFirst, hStepsFirst⟩
    have hTargetNe : res1 ≠ none := by
      intro hnone
      cases firstResult <;> simp_all [resultCase]
    refine ⟨t1, res1, ?_, hFfiFirst, hResultFirst, ?_⟩
    ·
      simp only [LoopToWord.compHOL]
      change WordSemStateFiniteExact.evaluate
        (.seq (LoopToWord.compHOL ctxt c1 l).1
          (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t =
          (res1, t1)
      rw [WordSemStateFiniteExact.evaluate]
      rw [WordSemStateFiniteExact.fix_clock_evaluate t (LoopToWord.compHOL ctxt c1 l).1]
      simp [hTargetFirst]
    · have hw := WordSteps.steps_seq (LoopToWord.compHOL ctxt c1 l).1
        (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1 t
      have hs := LoopSteps.steps_seq c1 c2 s
      rw [hTargetFirst] at hw
      rw [hFirstEval] at hs
      cases res1 with
      | none => exact False.elim (hTargetNe rfl)
      | some r =>
        simp only at hw hs
        simp only [LoopToWord.compHOL]
        change WordSteps.steps (.seq (LoopToWord.compHOL ctxt c1 l).1
          (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t ≤ _
        omega
  have hSourceSeq' := hSourceSeq
  simp only [LoopSemStateFiniteExact.evaluate] at hSourceSeq'
  rw [LoopSemStateFiniteExact.fix_clock_evaluate c1 s] at hSourceSeq'
  cases hFirstEval : LoopSemStateFiniteExact.evaluate c1 s with
  | mk firstResult firstState =>
    rw [hFirstEval] at hSourceSeq'
    cases firstResult with
    | none =>
      have hSourceSecond :
          LoopSemStateFiniteExact.evaluate c2 firstState = (res, sFinal) := hSourceSeq'
      have hFirstCase := hFirst none firstState t ctxt retv l
        ⟨hFirstEval, by simp, hState, hLocals, hRetv, hDim, hWord, hAccFirst⟩
      rcases hFirstCase with ⟨t1, res1, hTargetFirst, hFirstFfi, hFirstResultCase, hStepsFirst⟩
      rcases hFirstResultCase with ⟨hState1, hNone, hRetv1, hLocals1, hStack1, hHandler1⟩
      subst res1
      have hSecondCase := hSecond none firstState ⟨hFirstEval.symm, rfl⟩
      let l2 := (LoopToWord.compHOL ctxt c1 l).2
      have hTargetSecond := hSecondCase res sFinal t1 ctxt retv l2
        ⟨hSourceSecond, hNonError, hState1, hLocals1, hRetv1, hDim, hWord, hAccSecond⟩
      rcases hTargetSecond with ⟨t2, res2, hEvalSecond, hFfiSecond, hResultSecond, hStepsSecond⟩
      have hResult : resultCase ctxt retv t res sFinal res2 t2 := by
        simpa [resultCase, hStack1, hHandler1] using hResultSecond
      refine ⟨t2, res2, ?_, hFfiSecond, hResult, ?_⟩
      · simp only [LoopToWord.compHOL]
        change WordSemStateFiniteExact.evaluate
          (.seq (LoopToWord.compHOL ctxt c1 l).1
            (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t =
            (res2, t2)
        rw [WordSemStateFiniteExact.evaluate]
        rw [WordSemStateFiniteExact.fix_clock_evaluate t (LoopToWord.compHOL ctxt c1 l).1]
        simp [hTargetFirst, hEvalSecond, l2]
      · have hw := WordSteps.steps_seq (LoopToWord.compHOL ctxt c1 l).1
          (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1 t
        have hs := LoopSteps.steps_seq c1 c2 s
        rw [hTargetFirst] at hw
        rw [hFirstEval] at hs
        simp only at hw hs
        simp only [LoopToWord.compHOL]
        change WordSteps.steps (.seq (LoopToWord.compHOL ctxt c1 l).1
          (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 l).2).1) t ≤ _
        dsimp only [l2] at hStepsSecond
        omega
    | some result =>
      have hSourceFinal : res = some result ∧ sFinal = firstState := by
        simpa [hFirstEval, Option.some.injEq] using hSourceSeq'.symm
      rcases hSourceFinal with ⟨rfl, rfl⟩
      have hFirstNe : some result ≠ some LoopSemStateFiniteExact.LoopResultExact.error := by
        intro heq
        apply hNonError
        simpa using heq
      exact hPropagate result hFirstNe hFirstEval



/-- Marking a program adds one LoopSem visit and is erased by compilation. -/
theorem boundedMark {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (source : LoopSemStateFiniteExact width F)
    (body : BoundPropertyAt C p source) : BoundPropertyAt C (.mark p) source := by
  intro result sourcePost target ctxt retv labels premises
  have run : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) := by
    simpa only [LoopSemStateFiniteExact.evaluate] using premises.1
  have acc : ∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt := by
    simpa only [accVarsHOL] using premises.2.2.2.2.2.2.2
  obtain ⟨targetPost,targetResult,targetRun,ffi,relation,bound⟩ :=
    body result sourcePost target ctxt retv labels ⟨run,premises.2.1,premises.2.2.1,
      premises.2.2.2.1,premises.2.2.2.2.1,premises.2.2.2.2.2.1,
      premises.2.2.2.2.2.2.1,acc⟩
  refine ⟨targetPost,targetResult,?_,ffi,relation,?_⟩
  · simpa only [LoopToWord.compHOL] using targetRun
  · rw [LoopSteps.steps_mark]
    simpa only [LoopToWord.compHOL] using Nat.le_trans bound (Nat.le_add_left _ _)

/-- Direct leaves closed under sequencing and marks. -/
inductive DirectProgram {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : LoopSteps.DirectLeaf p → DirectProgram p
  | seq {a b} : DirectProgram a → DirectProgram b → DirectProgram (.seq a b)
  | mark {p} : DirectProgram p → DirectProgram (.mark p)

/-- A complete, unconditional quantitative Loop-to-Word simulation for
programs made of direct leaves, sequences, and marks. -/
theorem directProgram_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    {p : HolLoopProg width} (shape : DirectProgram p) :
    ∀ source : LoopSemStateFiniteExact width F, BoundPropertyAt C p source := by
  induction shape with
  | leaf leaf =>
    intro source result sourcePost target ctxt retv labels premises
    obtain ⟨targetPost,targetResult,run,ffi,relation,exactSteps⟩ :=
      LoopSteps.directLeaf_correct_with_steps _ leaf source sourcePost result target ctxt retv labels premises
    exact ⟨targetPost,targetResult,run,ffi,relation,by omega⟩
  | seq ha hb iha ihb =>
    intro source
    apply boundedSeq _ _ source
    exact ⟨fun _ middle _ => ihb middle,iha source⟩
  | mark hp ih =>
    intro source
    exact boundedMark _ source (ih source)

end SteppedFlapjack.LoopToWordSteps
