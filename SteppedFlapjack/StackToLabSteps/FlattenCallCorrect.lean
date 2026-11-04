import SteppedFlapjack.StackToLabSteps.FlattenCorrect
import Flapjack.Compiler.Backend.StackProps.EvaluateMono

/-! Adapted copy of `Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCallCorrect.lean`
(stepped-flapjack#2, phase C1). The original `flattenCallCorrect` becomes
`flattenCallCorrectWithin`, which bounds the LabSem run by
`flattenStepFactor` ticks per StackSem step of the procedure body. The entry
call itself runs no LabSem instruction: the run starts at the body. When the
body returns `Loc n 0`, the run continues into procedure `n`, whose steps the
hypothesis bounds by `h` (`haltStepsWithin` for procedure 1). `haltAssum` is
copied unchanged. The `@[hol]` attributes and the representation witnesses,
which only serve them, are dropped. Otherwise the proofs follow the original. -/

/-! `flatten_call_correct` (`stack_to_labProofScript.sml:2741-2825`): a whole
StackSem call of the start procedure is simulated by running its flattened
code from its entry point, and a returned `Loc n 0` reaches the halting
procedure `n` by the assumption on its call. -/

namespace SteppedFlapjack.StackToLabSteps
open Flapjack hiding flattenHOL
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
  (FlattenHyps FlattenConcl MeasureLt appListAppendList appListAppendAppend)
open SteppedFlapjack.StackSteps

/-- The two outcomes of a non-error whole call of a procedure: a clock-zero
timeout, or the evaluation of the found body at the decremented clock. -/
theorem callNoneInlCases {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 s2 : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)}
    (ev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s1) =
      (res, s2))
    (nerr : res ≠ some .error) :
    ∃ prog, sptLookup start s1.code = some prog ∧
      ((s1.clock = 0 ∧ res = some .timeOut ∧ s2 = StackSemStateOps.emptyEnv s1) ∨
       (s1.clock ≠ 0 ∧ ∃ x, res = some x ∧ StackSemControl.badFunReturn (some x) = false ∧
         StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) = (some x, s2))) := by
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  rcases hfind : StackSemControl.findCode (.inl start) s1.regs s1.code with _ | prog
  · rw [hfind] at ev; simp only [Prod.mk.injEq] at ev; exact (nerr ev.1.symm).elim
  rw [hfind] at ev
  simp only at ev
  have hlook : sptLookup start s1.code = some prog := by
    simpa [StackSemControl.findCode] using hfind
  refine ⟨prog, hlook, ?_⟩
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev; simp only [Prod.mk.injEq] at ev
    exact .inl ⟨h0, ev.1.symm, ev.2.symm⟩
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨r, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn r = true
  · rw [if_pos hbad] at ev; simp only [Prod.mk.injEq] at ev; exact (nerr ev.1.symm).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x, rfl⟩ := notBadFunReturnImpSome _ hbad
  exact .inr ⟨h0, x, rfl, by simpa using hbad, rfl⟩

/-- HOL `flatten_call_correct` with the LabSem run bounded: the run takes at
most `flattenStepFactor` ticks per StackSem step of the start procedure's body,
and, when the body returns `Loc n 0`, per step of procedure `n`, whose call
takes at most `hmax` steps. -/
theorem flattenCallCorrectWithin {width : Nat} [NeZero width] {C F : Type} {start hmax : Nat}
    {s1 s2 : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} :
    StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s1) = (res, s2) ∧
    stateRel s1 t1 ∧
    locToPc start 0 t1.code = some t1.pc ∧
    res ≠ some .error ∧
    (res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F, sptSubspt s1.code s.code ∧ s.clock ≠ 0 →
          (∃ t, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1) ∧
          steps ((.call none (.inl n) none : HolProg width), s) ≤ hmax)) →
    ∃ (ck : Nat) (r2 : MachineResult) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      t1.clock - 1 + ck ≤ t2.clock + flattenStepFactor *
        (steps ((.call none (.inl start) none : HolProg width), s1) - 1 + (hmax - 1)) ∧
      evaluate { t1 with clock := t1.clock - 1 + ck } = (r2, t2) ∧
      (∀ f, res = some (.finalFFI f) → r2 = .halt (.ffiOutcome f)) ∧
      (∀ w, res = some (.halt w) → r2 =
        match w with
        | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
        | _ => .error) ∧
      (∀ n, res = some (.result (.loc n 0)) → r2 = .halt .success) ∧
      t2.ffi = s2.ffi ∧
      r2 ≠ .error ∧ (res = some .timeOut → r2 = .timeOut) := by
  rintro ⟨ev, rel, hpc, nerr, hres⟩
  have clk := relClock rel
  obtain ⟨prog, hlook, ⟨h0, rfl, rfl⟩ | ⟨h0, x, rfl, hbad, e2⟩⟩ := callNoneInlCases ev nerr
  · -- clock zero: both sides time out at once
    refine ⟨0, .timeOut, { t1 with clock := t1.clock - 1 + 0 }, by simp, ?_, by simp, by simp,
      by simp, ?_, by simp, fun _ => rfl⟩
    · rw [evaluate, if_pos (by simp; omega)]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  have hsteps : steps ((.call none (.inl start) none : HolProg width), s1) =
      1 + steps (prog, StackSemStateOps.decClock s1) := by
    rw [steps_call_none]
    simp [StackSemControl.findCode, hlook, h0]
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  rw [hpc] at entry
  cases entry
  have rel' : stateRel (StackSemStateOps.decClock s1) { t1 with clock := t1.clock - 1 } :=
    StateRel.stateRelDecClock rel
  have nx : x ≠ .error := fun h => nerr (by rw [h])
  obtain ⟨ck, t2, hb, h⟩ := flattenPropAll prog (StackSemStateOps.decClock s1) true (some x) s2
    start (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] [] { t1 with clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [hpc]⟩
  simp only at hb
  have hb' : t1.clock - 1 + ck ≤ t2.clock + flattenStepFactor *
      (steps ((.call none (.inl start) none : HolProg width), s1) - 1 + (hmax - 1)) := by
    rw [hsteps]; simp only [flattenStepFactor] at hb ⊢; omega
  rcases x with v | v | k | k | v | _ | f | _
  · -- `Result v`: only `Loc n 0` is allowed, and procedure `n` halts
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, hh⟩ := hres (by simp)
    · simp at hw
    · simp at hf
    simp only [Option.some.injEq, StackSemResult.result.injEq] at hn
    subst hn
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hcover, hw⟩ := h
    have hsub : sptSubspt s1.code s2.code := by
      simpa [StackSemStateOps.decClock] using
          (Compiler.Backend.StackProps.EvaluateMono.evaluateMono _ _ _ _ e2).2
    obtain ⟨⟨t, evh, tffi, -⟩, hsth⟩ := hh { s2 with clock := s2.clock + 1 } ⟨hsub, by simp⟩
    obtain ⟨prog2, hlook2, ⟨h0', -⟩ | ⟨-, x2, hx2, -, e3⟩⟩ := callNoneInlCases evh (by simp)
    · simp at h0'
    simp only [Option.some.injEq] at hx2
    subst hx2
    have hdc : StackSemStateOps.decClock { s2 with clock := s2.clock + 1 } = s2 := by
      simp [StackSemStateOps.decClock]
    have hsteps2 : steps ((.call none (.inl n) none : HolProg width),
        { s2 with clock := s2.clock + 1 }) = 1 + steps (prog2, s2) := by
      rw [steps_call_none]
      simp [StackSemControl.findCode, hlook2, hdc]
    rw [hdc] at e3
    simp only at hlook2
    obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp (hcover n (by simp [hlook2]))
    obtain ⟨rfl, rel2⟩ := hw w hw'
    obtain ⟨caP2, pc2, instP2, entry2⟩ := relCode rel2 hlook2
    rw [hw'] at entry2
    cases entry2
    obtain ⟨ck', t3, hb3, h3⟩ := flattenPropAll prog2 s2 true (some (.halt (.word 0))) t n
      (Compiler.Backend.StackAlloc.nextLabHOL prog2 2) [] [] t2 ⟨e3, by simp, rel2, caP2, instP2,
          by simp [hw']⟩
    simp only [haltView, haltWordView, if_true] at h3
    refine ⟨ck + ck', .halt .success, t3, ?_, ?_, by simp, by simp, fun _ _ => rfl, ?_, by simp,
      by simp⟩
    · rw [hsteps]
      rw [hsteps2] at hsth
      simp only [flattenStepFactor] at hb hb3 ⊢
      omega
    · have r1 := run ck'
      rw [show t1.clock - 1 + (ck + ck') = t1.clock - 1 + ck + ck' by omega, r1]
      exact h3.1
    · rw [h3.2, tffi]
  · -- `Exception`: excluded by the hypothesis
    rcases hres (by simp) with ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩
    · simp at hw
    · simp at hf
    · simp at hn
  · simp [StackSemControl.badFunReturn] at hbad
  · simp [StackSemControl.badFunReturn] at hbad
  · -- `Halt v`
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩ := hres (by simp)
    · simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw
      subst hw
      simp only [haltView] at h
      refine ⟨ck, haltWordView (.word w), t2, hb', h.1, by simp, ?_, by simp, h.2, ?_, by simp⟩
      · intro w' hw'
        simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw'
        subst hw'
        rfl
      · simp only [haltWordView]; split <;> simp
    · simp at hf
    · simp at hn
  · -- `TimeOut`
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hffi, hclk⟩ := h
    refine ⟨ck, .timeOut, { t2 with clock := t2.clock + 0 }, hb', ?_, by simp, by simp, by simp,
      hffi, by simp, fun _ => rfl⟩
    have r0 := run 0
    simp only [Nat.add_zero] at r0 ⊢
    rw [r0, evaluate, if_pos (by simp [hclk])]
  · -- `FinalFFI f`
    simp only [haltView] at h
    exact ⟨ck, _, t2, hb', h.1, by intro f' hf'; cases hf'; rfl, by simp, by simp, h.2, by simp,
      by simp⟩
  · exact (nx rfl).elim

/-- HOL `halt_assum_def`: every StackSem state whose code extends `code` and
whose clock is nonzero halts with `Word 0w` when calling procedure 1, using one
clock tick and no FFI. The HOL type argument `(:('ffi#'c))` is the explicit
`C F`. -/
def haltAssum {width : Nat} [NeZero width] (C F : Type)
    (code : Spt (HolProg width)) : Prop := ∀ s : StackSemStateFiniteExact width C F,
    sptSubspt code s.code ∧ s.clock ≠ 0 →
    ∃ t, StackSemEvaluate.evaluate ((.call none (.inl 1) none : HolProg width), s) =
        (some (.halt (.word (0 : BitVec width))), t) ∧
      t.ffi = s.ffi ∧ t.clock = s.clock - 1

/-- The halting call of procedure 1 from every state allowed by `haltAssum`
takes at most `h` StackSem steps (stepped-flapjack infrastructure). -/
def haltStepsWithin {width : Nat} [NeZero width] (C F : Type)
    (code : Spt (HolProg width)) (h : Nat) : Prop := ∀ s : StackSemStateFiniteExact width C F,
    sptSubspt code s.code ∧ s.clock ≠ 0 →
    steps ((.call none (.inl 1) none : HolProg width), s) ≤ h

end SteppedFlapjack.StackToLabSteps
