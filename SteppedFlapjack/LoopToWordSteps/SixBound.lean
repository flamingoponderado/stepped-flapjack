import SteppedFlapjack.LoopToWordSteps.LoopCost
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.If

/-! A sixfold Loop-to-Word step bound including conditionals. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect
open Flapjack.Compiler.Encoders.Asm

def SixBoundPropertyAt {width : Nat} [NeZero width] (C : Type) {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) : Prop :=
  ∀ (res : Option (LoopResultExact width)) (s1 : LoopSemStateFiniteExact width F)
    (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
    LoopSemStateFiniteExact.evaluate p s = (res,s1) ∧ res ≠ some .error ∧
      loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
      sptLookup 0 t.locals = some retv ∧ goodDimindex width ∧ ¬ wordSemIsWordLoc retv = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) →
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p l).1 t = (res1,t1) ∧
      t1.ffi = s1.ffi ∧ resultCase ctxt retv t res s1 res1 t1 ∧
      WordSteps.steps (LoopToWord.compHOL ctxt p l).1 t ≤ 6 * LoopSteps.steps p s

/-- Quantitative sequential composition, preserving all original result cases. -/
theorem sixBoundedSeq {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    ((∀ res s1, (res, s1) = LoopSemStateFiniteExact.evaluate c1 s ∧ res = none →
        SixBoundPropertyAt C c2 s1) ∧ SixBoundPropertyAt C c1 s) →
      SixBoundPropertyAt C (.seq c1 c2) s := by
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
          WordSteps.steps (LoopToWord.compHOL ctxt (.seq c1 c2) l).1 t ≤ 6 * LoopSteps.steps (.seq c1 c2) s := by
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
theorem sixBoundedMark {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (source : LoopSemStateFiniteExact width F)
    (body : SixBoundPropertyAt C p source) : SixBoundPropertyAt C (.mark p) source := by
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
    simp only [LoopToWord.compHOL]
    omega


theorem sixBoundedIf {width : Nat} [NeZero width] {C F : Type}
    (cmp : Cmp) (r1 : Nat) (ri : RegImm (BitVec width)) (c1 c2 : HolLoopProg width)
    (live : NumSet) (s : LoopSemStateFiniteExact width F)
    (ih : ∀ (v2 v3 : Option (WordLocW width)) (v5 : WordLocW width) (x : BitVec width)
        (v13 : WordLocW width) (y : BitVec width) (b : Bool),
      (sptLookup r1 s.locals, LoopSemStateFiniteExact.getVarImm ri s) = (v2, v3) →
      v2 = some v5 → v5 = .word x → v3 = some v13 → v13 = .word y →
      b = Compiler.Encoders.Asm.wordCmpHOL cmp x y →
      SixBoundPropertyAt C (if b then c1 else c2) s) :
    ∀ (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (final : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
      (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat),
      LoopSemStateFiniteExact.evaluate (.ite cmp r1 ri c1 c2 live) s = (res, final) ∧
        res ≠ some .error ∧ loopToWordStateRelHOLExact s t ∧
        localsRelHOL ctxt s.locals t.locals ∧ sptLookup 0 t.locals = some retv ∧
        goodDimindex width ∧ ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL (.ite cmp r1 ri c1 c2 live) .ln) → sptMem k ctxt) →
      ∃ tf rf,
        WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt (.ite cmp r1 ri c1 c2 live) l).1 t =
          (rf, tf) ∧ tf.ffi = final.ffi ∧ resultCase ctxt retv t res final rf tf ∧
          WordSteps.steps (LoopToWord.compHOL ctxt (.ite cmp r1 ri c1 c2 live) l).1 t ≤ 6 * LoopSteps.steps (.ite cmp r1 ri c1 c2 live) s := by
  intro res final t ctxt retv l ⟨heval, hne, hstate, hlocals, hret, hdim, hword, hacc⟩
  have hchildAcc (b : Bool) :
      ∀ k, sptMem k (accVarsHOL (if b then c1 else c2) .ln) → sptMem k ctxt := by
    intro k hk
    have hs : sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k ↔
        sptDomain (accVarsHOL c1 .ln) k ∨ sptDomain (accVarsHOL c2 .ln) k := by
      rw [accVarsAccHOL c1 (accVarsHOL c2 .ln)]
    apply hacc k
    change sptDomain (accVarsHOL c1 (accVarsHOL c2 .ln)) k
    apply hs.mpr
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hk
    · exact Or.inr hk
    · exact Or.inl hk
  simp only [LoopSemStateFiniteExact.evaluate] at heval
  cases hx : sptLookup r1 s.locals with
  | none => simp [hx] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
  | some xv =>
    cases xv with
    | loc a b => simp [hx] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
    | word x =>
      cases hy : LoopSemStateFiniteExact.getVarImm ri s with
      | none => simp [hx, hy] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
      | some yv =>
        cases yv with
        | loc a b => simp [hx, hy] at heval; obtain ⟨rfl, rfl⟩ := heval; exact False.elim (hne rfl)
        | word y =>
          let b := Compiler.Encoders.Asm.wordCmpHOL cmp x y
          let child := if b then c1 else c2
          have hprop : SixBoundPropertyAt C child s :=
            ih _ _ _ x _ y b (by rw [hx, hy]) rfl rfl rfl rfl rfl
          have htx := localsRelHOLGetVar ctxt s.locals t r1 (.word x) ⟨hlocals, hx⟩
          let targetRi : WordRegImm (BitVec width) :=
            match (generalizing := false) ri with
            | .imm w => .imm w
            | .reg n => .reg (findVarHOL ctxt n)
          have hty : WordSemStateFiniteExact.getVarImm targetRi t = some (.word y) := by
            cases ri with
            | imm w => simpa [LoopSemStateFiniteExact.getVarImm, targetRi,
                WordSemStateFiniteExact.getVarImm] using hy
            | reg n => exact localsRelHOLGetVar ctxt s.locals t n (.word y) ⟨hlocals, hy⟩
          have hcut : LoopSemStateFiniteExact.cutRes live
              (LoopSemStateFiniteExact.evaluate child s) = (res, final) := by
            cases hb : b <;> simpa [hx, hy, child, b, hb] using heval
          rcases hc : LoopSemStateFiniteExact.evaluate child s with ⟨cr, cs⟩
          have hcne : cr ≠ some .error := by
            intro h
            simp [hc, h, LoopSemStateFiniteExact.cutRes] at hcut
            obtain ⟨rfl, rfl⟩ := hcut
            exact hne rfl
          obtain ⟨ct, tr, htarget, hffi, hr, hsteps⟩ := hprop cr cs t ctxt retv
            (if b then l else (LoopToWord.compHOL ctxt c1 l).2)
            ⟨hc, hcne, hstate, hlocals, hret, hdim, hword, hchildAcc b⟩
          obtain ⟨tf, rf, htick, hff, hresult⟩ :=
            handlerTail ctxt retv t t live cr cs tr ct res final hr hffi rfl rfl
              (by simpa [hc] using hcut) hne
          refine ⟨tf, rf, ?_, hff, hresult, ?_⟩
          · rcases hcomp1 : LoopToWord.compHOL ctxt c1 l with ⟨wc1, labels1⟩
            rcases hcomp2 : LoopToWord.compHOL ctxt c2 labels1 with ⟨wc2, labels2⟩
            unfold LoopToWord.compHOL
            simp only [hcomp1, hcomp2]
            change WordSemStateFiniteExact.evaluate
              (.seq (.ite cmp (findVarHOL ctxt r1) targetRi
                wc1 wc2) .tick) t =
              (rf, tf)
            rw [WordSemStateFiniteExact.evaluate,
              WordSemStateFiniteExact.fix_clock_evaluate]
            have hchoose : WordSemStateFiniteExact.evaluate
                (.ite cmp (findVarHOL ctxt r1) targetRi
                  wc1 wc2) t =
                (tr, ct) := by
              rw [WordSemStateFiniteExact.evaluate]
              simp only [htx, hty, wordSemWordCmp]
              cases hb : b <;> simpa [child, b, hb, hcomp1, hcomp2] using htarget
            rw [hchoose]
            cases tr <;> exact htick
          · rcases hcomp1 : LoopToWord.compHOL ctxt c1 l with ⟨wc1, labels1⟩
            rcases hcomp2 : LoopToWord.compHOL ctxt c2 labels1 with ⟨wc2, labels2⟩
            have hchoose : WordSemStateFiniteExact.evaluate
                (.ite cmp (findVarHOL ctxt r1) targetRi wc1 wc2) t = (tr,ct) := by
              rw [WordSemStateFiniteExact.evaluate]
              simp only [htx, hty, wordSemWordCmp]
              cases hb : b <;> simpa [child,b,hb,hcomp1,hcomp2] using htarget
            have hs := LoopSteps.steps_ite cmp r1 ri c1 c2 live s
            rw [hx,hy] at hs
            have hi := WordSteps.steps_ite cmp (findVarHOL ctxt r1) targetRi wc1 wc2 t
            rw [htx,hty] at hi
            simp only [wordSemWordCmp] at hi
            have hw := WordSteps.steps_seq (.ite cmp (findVarHOL ctxt r1) targetRi wc1 wc2) .tick t
            rw [hchoose] at hw
            have tick : WordSteps.steps (.tick : WordLangProgHOL (BitVec width)) ct = 1 := WordSteps.steps_leaf _ _ rfl
            cases hb : b <;> simp only [child,b,hb,Bool.false_eq_true,↓reduceIte,hcomp1,hcomp2] at hsteps hs
            all_goals simp only [b,hb] at hi
            all_goals cases tr <;> simp only [tick] at hw
            all_goals unfold LoopToWord.compHOL
            all_goals simp only [hcomp1,hcomp2]
            all_goals change WordSteps.steps (.seq (.ite cmp (findVarHOL ctxt r1) targetRi wc1 wc2) .tick) t ≤ _
            all_goals omega



end SteppedFlapjack.LoopToWordSteps
