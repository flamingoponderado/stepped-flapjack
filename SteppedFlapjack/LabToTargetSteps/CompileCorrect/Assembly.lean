import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Install
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Control
import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Cbw

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Assembly.lean`
(stepped-flapjack#2, phase B). The cases are assembled into
`compileCorrectWithinFor_all` by the same strong induction on the source clock.
The original `compileCorrect` becomes `compileCorrectWithin`, whose hypotheses
are `encoderCorrectWithin mc.target steps` and `StepsFit unit steps mc.target`
instead of `encoderCorrect mc.target`, and whose conclusion bounds the extra
target ticks by `(labTickBound unit code2 s1.codeBuffer - 1) * s1.clock`; the
unused `t2` is dropped. `compileCorrectWithin_total` restates the bound in total
ticks and `compileCorrect_of_within` recovers the original statement. The
`@[hol]` attributes are dropped. Otherwise the proofs follow the original. -/

/-! The original `compile_correct` (lab_to_targetProofScript.sml:7528-7558),
assembled from its cases by the source's `evaluate_ind` induction, which this
file realises as strong induction on the source clock: every recursive call
of `LabSem.evaluate` runs on a state whose clock is one less. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- A source state whose evaluation is an `Error` satisfies the conclusion
vacuously (the original's `res <> Error` premise). -/
theorem compileCorrect_error {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (h : evaluate s1 = (.error, s1)) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, hres, -, -, -⟩
  rw [h] at hev
  exact absurd (Prod.mk.inj hev).1.symm hres

/-- A timed-out source state is matched by the target with no extra clock. -/
theorem compileCorrect_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (hc : s1.clock = 0) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, -, -, -, -⟩
  rw [evaluate, if_pos hc] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  exact ⟨0, ms1, Nat.zero_le _, by rw [hc]; rfl⟩

/-- Every source state satisfies the original `compile_correct` conclusion:
the cases of the original proof, combined by strong induction on the source
clock (the original's `evaluate_ind`). -/
theorem compileCorrectWithinFor_all {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) : CompileCorrectWithinFor S Q unit steps s1 := by
  induction hcl : s1.clock using Nat.strong_induction_on generalizing s1 with
  | _ c ihc =>
  have IH : ∀ s' : LabSem.State width Config F, s'.clock < s1.clock →
      CompileCorrectWithinFor S Q unit steps s' := fun s' hs => ihc _ (hcl ▸ hs) s' rfl
  by_cases hc : s1.clock = 0
  · exact compileCorrect_timeOut s1 hc
  have herr : ∀ (h : evaluate s1 = (.error, s1)), CompileCorrectWithinFor S Q unit steps s1 :=
    compileCorrect_error s1
  cases hf : asmFetch s1 with
  | none => exact herr (by rw [evaluate]; simp [hc, hf])
  | some line =>
  cases line with
  | label => exact herr (by rw [evaluate]; simp [hc, hf])
  | asm a bytes n =>
    cases a with
    | asmi i =>
      cases i with
      | inst ins =>
        exact compileCorrect_asmInst s1 ins bytes n hc hf fun _ => IH _ (by
          obtain ⟨-, -, hcl', -⟩ := asmInstConsts ins s1
          simp [incPc, decClock, hcl']; omega)
      | jumpReg r =>
        exact compileCorrect_jumpReg s1 r bytes n hc hf fun _ _ _ _ _ => IH _ (by
          simp [LabSem.updPc, decClock]; omega)
      | _ => exact herr (by rw [evaluate]; simp [hc, hf])
    | cbw r1 r2 =>
      exact compileCorrect_cbw s1 r1 r2 bytes n hc hf fun _ _ _ _ _ _ => IH _ (by
        simp [incPc, decClock]; omega)
    | shareMem m r ad =>
      exact compileCorrect_shareMem s1 m r ad bytes n hc hf fun ffi' bs s' hs => IH _ (by
        have := shareMemOp_ret_clock m r ad s1 s' ffi' bs hs
        simp only; omega)
  | labAsm a w bytes n =>
    cases a with
    | jump jt =>
      exact compileCorrect_jump s1 jt w bytes n hc hf fun _ _ => IH _ (by
        simp [LabSem.updPc, decClock]; omega)
    | jumpCmp cmp rr ri jt =>
      exact compileCorrect_jumpCmp s1 cmp rr ri jt w bytes n hc hf
        (fun _ => IH _ (by simp [incPc, decClock]; omega))
        (fun _ _ _ => IH _ (by simp [LabSem.updPc, decClock]; omega))
    | call lab =>
      exact compileCorrect_call s1 lab w bytes n hc hf fun _ _ _ _ => IH _ (by
        simp [LabSem.updPc, decClock, LabSem.updReg]; omega)
    | locValue reg lab =>
      exact compileCorrect_locValue s1 reg lab w bytes n hc hf fun _ => IH _ (by
        simp [incPc, decClock, LabSem.updReg]; omega)
    | install =>
      exact compileCorrect_install s1 w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega)
    | callFFI name =>
      exact compileCorrect_callFFI s1 name w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega)
    | halt => exact compileCorrect_halt s1 w bytes n hc hf

/-- The original `compile_correct` with the target run bounded: for an
encoder correct within `steps` ticks per instruction with
`StepsFit unit steps`, the target evaluated at clock `s1.clock + k` gives the
source result for some `k ≤ (L - 1) * s1.clock`, where
`L = labTickBound unit code2 s1.codeBuffer` bounds the ticks of one source
instruction. The unused `t2` of the original is omitted. -/
theorem compileCorrectWithin {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (unit : Nat) (steps : HolAsm width → Nat)
    (p : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (s2 : Flapjack.Compiler.Backend.LabSem.State width Config F) (code2 : LabProgHOL width)
    (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S) :
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectWithin mc.target steps ∧ StepsFit unit steps mc.target ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1 →
    ∃ (k : Nat) (ms2 : S), k ≤ (labTickBound unit code2 s1.codeBuffer - 1) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi) :=
  fun h => compileCorrectWithinFor_all s1 res mc s2 code2 labs t1 ms1 p h

/-- `compileCorrectWithin` counted in total target ticks: the target evaluated
at some clock `n` with `s1.clock ≤ n ≤ L * s1.clock` gives the source result,
where `L = labTickBound unit code2 s1.codeBuffer`. `n` is a sufficient clock,
so `L * s1.clock` bounds the ticks used; the lower bound says nothing about
them. -/
theorem compileCorrectWithin_total {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (unit : Nat) (steps : HolAsm width → Nat)
    (p : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (s2 : Flapjack.Compiler.Backend.LabSem.State width Config F) (code2 : LabProgHOL width)
    (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (h : oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectWithin mc.target steps ∧ StepsFit unit steps mc.target ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ (n : Nat) (ms2 : S), s1.clock ≤ n ∧
      n ≤ labTickBound unit code2 s1.codeBuffer * s1.clock ∧
      evaluateTargetHOL mc s1.ffi n ms1 = (res, ms2, s2.ffi) := by
  obtain ⟨k, ms2, hk, he⟩ := compileCorrectWithin unit steps p s1 res mc s2 code2 labs t1 ms1 h
  refine ⟨s1.clock + k, ms2, Nat.le_add_right _ _, ?_, he⟩
  simp only [labTickBound, Nat.add_sub_cancel] at hk ⊢
  rw [Nat.succ_mul]
  omega

/-- Dropping the bound gives the statement of the original `compile_correct`
(`compileCorrect`), with its unused `t2` over an arbitrary nonempty `T`, from
the bounded encoder hypotheses. -/
theorem compileCorrect_of_within {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    {T : Type} [Nonempty T] (unit : Nat) (steps : HolAsm width → Nat)
    (p : BitVec width) (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (s2 : Flapjack.Compiler.Backend.LabSem.State width Config F) (code2 : LabProgHOL width)
    (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S) :
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectWithin mc.target steps ∧ StepsFit unit steps mc.target ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1 →
    ∃ (k : Nat) (_t2 : T) (ms2 : S),
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi) := by
  intro h
  obtain ⟨k, ms2, -, hk⟩ := compileCorrectWithin unit steps p s1 res mc s2 code2 labs t1 ms1 h
  exact ⟨k, Classical.arbitrary T, ms2, hk⟩

end SteppedFlapjack.LabToTargetSteps
