import SteppedFlapjack.StackToLabSteps.FlattenCallCorrect
import SteppedFlapjack.StackToLabSteps.LabClock
import Flapjack.Pancake.CrepToLoop.Proofs.SemanticsWrapper

/-! Adapted copy of the parts of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenSemantics.lean` that a
bounded `flatten_semantics` needs (stepped-flapjack#2, phase C1): the run
classifications `stackEntryClass` and `labEntryClass`, copied unchanged.
The semantics-wrapper argument of the original is not copied. In its place,
`flattenSemanticsWithin` bounds the LabSem run that matches one terminating
StackSem entry run: if the entry run from clock `k` completes with outcome
`o` within `n` steps, the LabSem run from clock at most
`flattenStepFactor * (n + h)` halts with `o` and the same I/O events. The
bound `h` on the steps of the halting procedure 1 (`haltStepsWithin`) is only
needed when the entry run returns `Loc 1 0`; otherwise `h = 0` will do.
`LabClock.evaluate_subClock` removes the clock the LabSem run does not need. -/

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

open Classical in
/-- The StackSem entry-run classification matching `stackSem$semantics_def`
(Flapjack infrastructure). -/
noncomputable def stackEntryClass {width : Nat} [NeZero width] :
    Option (StackSemResult width) → CrepToLoopSemanticsRunRes HolOutcome
  | some .timeOut => .Incomplete
  | some (.finalFFI e) => .CompleteResult (HolOutcome.ffiOutcome e)
  | some (.halt (.word w)) =>
      .CompleteResult (if w = 0 then HolOutcome.success else HolOutcome.resourceLimitHit)
  | some (.result r) => if r = .loc 1 0 then .CompleteResult HolOutcome.success else .RunError
  | _ => .RunError

/-- The LabSem run classification matching `labSem$semantics_def`
(Flapjack infrastructure). -/
def labEntryClass : MachineResult → CrepToLoopSemanticsRunRes HolOutcome
  | .halt o => .CompleteResult o
  | .timeOut => .Incomplete
  | .error => .RunError

/-- Bounded `flatten_semantics` for one terminating entry run: under the
hypotheses of `flatten_semantics`, a StackSem entry run from clock `k` that
completes with outcome `o` within `n` steps is matched by a LabSem run from
clock `m ≤ flattenStepFactor * (n + h)` that halts with `o` and the same I/O
events. -/
theorem flattenSemanticsWithin {width : Nat} [NeZero width] {C F : Type} {start k n h : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {res : Option (StackSemResult width)} {s' : StackSemStateFiniteExact width C F}
    {o : HolOutcome}
    (halt : haltAssum C F s1.code) (rel : stateRel s1 s2)
    (hpc : locToPc start 0 s2.code = some s2.pc)
    (hhalt : res = some (.result (.loc 1 0)) → haltStepsWithin C F s1.code h)
    (ev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s1 with clock := k }) = (res, s'))
    (hn : steps ((.call none (.inl start) none : HolProg width), { s1 with clock := k }) ≤ n)
    (hres : stackEntryClass res = .CompleteResult o) :
    ∃ m ≤ flattenStepFactor * (n + h), ∃ t',
      evaluate { s2 with clock := m } = (.halt o, t') ∧ t'.ffi.ioEvents = s'.ffi.ioEvents := by
  have nerr : res ≠ some .error := by rintro rfl; simp [stackEntryClass] at hres
  have hres' : res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n', res = some (.result (.loc n' 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F,
          sptSubspt { s1 with clock := k }.code s.code ∧ s.clock ≠ 0 →
          (∃ t, StackSemEvaluate.evaluate ((.call none (.inl n') none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1) ∧
          steps ((.call none (.inl n') none : HolProg width), s) ≤ h) := by
    intro hto
    rcases res with _ | x
    · simp [stackEntryClass] at hres
    rcases x with v | v | _ | _ | v | _ | e | _
    · rcases v with w | ⟨a, b⟩
      · simp [stackEntryClass] at hres
      · by_cases hab : a = 1 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := hab
          exact .inr (.inr ⟨1, rfl, fun s hs => ⟨halt s hs, hhalt rfl s hs⟩⟩)
        · simp_all [stackEntryClass]
    · simp [stackEntryClass] at hres
    · simp [stackEntryClass] at hres
    · simp [stackEntryClass] at hres
    · rcases v with w | ⟨a, b⟩
      · exact .inl ⟨w, rfl⟩
      · simp [stackEntryClass] at hres
    · exact absurd rfl hto
    · exact .inr (.inl ⟨e, rfl⟩)
    · simp [stackEntryClass] at hres
  obtain ⟨ck, r2, t2, hb, he2, hf, hh, hrs, hffi, -, hto⟩ :=
    flattenCallCorrectWithin (start := start) (hmax := h) (s1 := { s1 with clock := k })
      (t1 := { s2 with clock := k }) (res := res) (s2 := s')
      ⟨ev, stateRelWithClock rel, by simpa using hpc, nerr, hres'⟩
  have hr2 : r2 = .halt o := by
    rcases res with _ | x
    · simp [stackEntryClass] at hres
    rcases x with v | v | _ | _ | v | _ | e | _
    · rcases v with w | ⟨a, b⟩
      · simp [stackEntryClass] at hres
      · by_cases hab : a = 1 ∧ b = 0
        · obtain ⟨rfl, rfl⟩ := hab
          rw [hrs 1 rfl]
          simpa [stackEntryClass] using hres
        · simp_all [stackEntryClass]
    · simp [stackEntryClass] at hres
    · simp [stackEntryClass] at hres
    · simp [stackEntryClass] at hres
    · rcases v with w | ⟨a, b⟩
      · rw [hh _ rfl]
        simp only [stackEntryClass] at hres
        split_ifs at hres ⊢ <;> simp_all
      · simp [stackEntryClass] at hres
    · simp [stackEntryClass] at hres
    · rw [hf e rfl]
      simpa [stackEntryClass] using hres
    · simp [stackEntryClass] at hres
  subst hr2
  simp only at hb he2
  have hpos := steps_pos (.call none (.inl start) none : HolProg width) { s1 with clock := k }
  by_cases hT : k - 1 + ck ≤ flattenStepFactor *
      (steps ((.call none (.inl start) none : HolProg width), { s1 with clock := k }) - 1 +
        (h - 1)) + 1
  · refine ⟨k - 1 + ck, ?_, t2, he2, by rw [hffi]⟩
    simp only [flattenStepFactor] at *
    omega
  · refine ⟨flattenStepFactor *
      (steps ((.call none (.inl start) none : HolProg width), { s1 with clock := k }) - 1 +
        (h - 1)) + 1, ?_, _,
      evaluate_lowerClock { s2 with clock := k - 1 + ck } _ _ t2 he2 (by simp only; omega)
        (by simp only; omega), by simp [hffi]⟩
    simp only [flattenStepFactor] at *
    omega

end SteppedFlapjack.StackToLabSteps
