import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Step
import Flapjack.Compiler.Backend.LabToTarget.InstLemma
import Flapjack.Compiler.Backend.LabToTarget.AlignedPosVal

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Asm.lean`
(stepped-flapjack#2, phase B): the `Asmi (Inst i)` and `Asmi (JumpReg r)` cases
for `CompileCorrectWithinFor`. The simulated line takes `l` ticks with
`unit * l` at most its byte length, which is at most `maxLineBytes code2`;
`asmInst_codeBuffer` is added for the tick bound of the next state. The
`@[hol]` attributes are dropped. Otherwise the statements and proofs follow
the original. -/

namespace Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- A source instruction leaves the code buffer unchanged (stepped-flapjack
infrastructure, proved as `asmInstConsts`). -/
theorem _root_.SteppedFlapjack.LabToTargetSteps.asmInst_codeBuffer
    {width : Nat} [NeZero width] {C F : Type}
    (instruction : HolInst width) (state : State width C F) :
    (asmInst instruction state).codeBuffer = state.codeBuffer := by
  cases instruction with
  | skip => simp [asmInst]
  | const register value => simp [asmInst, updReg]
  | arith operation =>
      cases operation <;> simp only [asmInst, arithUpd]
      all_goals repeat' first
        | simp_all [binopUpd, updReg, assertState]
        | split
  | mem operator register address =>
      cases operator <;> simp only [asmInst, memOp, memLoad, memStore,
        memLoad32, memStore32, memLoadByte, memStoreByte]
      all_goals repeat' first
        | simp_all [updReg, updMem, assertState]
        | split
  | fp operation =>
      cases operation <;> simp only [asmInst, fpUpd]
      all_goals repeat' first
        | simp_all [updFpReg, updReg, assertState]
        | split

end Flapjack.Compiler.Backend.LabSem

/-! `Asm` cases of the original `compile_correct`
(lab_to_targetProofScript.sml:7560-7717): `Asmi (Inst i)` and
`Asmi (JumpReg r)`. Hypotheses are the source theorem's together with exactly
the `evaluate_ind` induction hypothesis of the instruction's recursive call. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

theorem compileCorrect_asmInst {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (i : HolInst width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (ih : ¬ (asmInst i s1).failed →
      CompileCorrectWithinFor S Q unit steps (incPc (decClock (asmInst i s1)))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  by_cases hf : (asmInst i s1).failed = true
  · simp only [hf, ↓reduceIte, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hev
    obtain ⟨bytes', len', hok, hmem, hpos, hdis, hbl⟩ :=
      fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
    simp only [lineOk, cbwToAsmHOL] at hok
    obtain ⟨htf, hout, hpost⟩ := instLemma i s1 mc code2 labs p t1 ms1 bytes' ms1
      ⟨hf, hrel, hpos⟩
    obtain ⟨l, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hfit (.inst i) bytes' hmem hok.1 hok.2.2
      hdis
      (by simpa [asmUpd, AsmSem.updPc] using htf)
      (fun a ha => by simpa [asmUpd, AsmSem.updPc] using hout a ha) (by intro x h; cases h)
    have hrel1 := (instLemma i s1 mc code2 labs p t1 ms1 bytes' ms2 ⟨hf, hrel, hpos⟩).2.2
      (hl 0).2.2.1
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel1
    obtain ⟨hpc, hcode, hcl, hffi, hio, hiofp, hcc, hccfp, -⟩ := asmInstConsts i s1
    exact compileCorrect_step (s1' := incPc (decClock (asmInst i s1))) ht hec hfit hclock
      (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
      (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl)
        (by simp [incPc, decClock, asmInst_codeBuffer])
      ⟨by simp [incPc, decClock, hcl], hffi, hio, hiofp, hcc, hccfp⟩ hrel' hev hres (ih hf)

/-- Aligned words sum to an aligned word; Flapjack infrastructure for HOL's
`aligned_add_sub_cor`. -/
theorem holAligned_add {width : Nat} [NeZero width] (a : Nat) (x y : BitVec width)
    (hx : holAligned a x = true) (hy : holAligned a y = true) : holAligned a (x + y) = true := by
  rw [LabToTarget.holAligned_iff] at hx hy ⊢
  rw [BitVec.toNat_add]
  rcases Nat.le_total a width with h | h
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.add_mod, hx, hy]; simp
  · have hx0 : x.toNat = 0 := by
      have := x.isLt
      have : x.toNat < 2 ^ a := lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) h)
      rw [Nat.mod_eq_of_lt this] at hx; exact hx
    have hy0 : y.toNat = 0 := by
      have := y.isLt
      have : y.toNat < 2 ^ a := lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) h)
      rw [Nat.mod_eq_of_lt this] at hy; exact hy
    simp [hx0, hy0]

/-- The `state_rel` mask form of code-base alignment; Flapjack infrastructure
for HOL's `aligned_bitwise_and`. -/
theorem holAligned_of_and_mask {width : Nat} [NeZero width] (a : Nat) (p : BitVec width)
    (h : (p &&& BitVec.ofNat width (2 ^ a - 1)) = 0) : holAligned a p = true := by
  rw [LabToTarget.holAligned_iff]
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  have h0 : (0 : BitVec width).toNat = 0 := by simp
  rw [h0] at h'
  rcases Nat.le_total a width with ha | ha
  · rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos a) (by decide))
      (Nat.pow_le_pow_right (by decide) ha)), Nat.and_two_pow_sub_one_eq_mod] at h'
    exact h'
  · have hm : (2 ^ a - 1) % 2 ^ width = 2 ^ width - 1 := by
      obtain ⟨c, hc⟩ : 2 ^ width ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
      have hpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, Nat.mul_zero] at hc; exact absurd hc (Nat.two_pow_pos a).ne'
        · exact h0
      rw [hc]
      have hw := Nat.two_pow_pos width
      rw [show 2 ^ width * c - 1 = 2 ^ width * (c - 1) + (2 ^ width - 1) by
        have hle := Nat.le_mul_of_pos_right (2 ^ width) hpos
        rw [Nat.mul_sub_one]; omega]
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt p.isLt] at h'
    simp [h']

/-- Every code position relative to the code base is an aligned jump
target; Flapjack infrastructure for the `JumpReg` alignment obligation. -/
theorem stateRel_aligned_target {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) (hec : encoderCorrect mc.target)
    (pc : Nat) :
    holAligned mc.target.config.codeAlignment (p + BitVec.ofNat width (posVal pc 0 code2)) =
      true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, c42, -, -, c45, -, c47, -⟩ := hrel
  rw [c45] at c42
  refine holAligned_add _ _ _ (holAligned_of_and_mask _ _ c42) ?_
  exact allEncOk_aligned_posVal mc labs code2 pc _ ⟨c47, fun ho =>
    hasOddInst_alignment _ labs _ 0 code2 ⟨hec.1.1, c47, ho⟩, hec⟩

theorem compileCorrect_jumpReg {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (r : Nat) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg r)) bytes n))
    (ih : ∀ n1 n2 pc, s1.regs r = .loc n1 n2 → locToPc n1 n2 s1.code = some pc →
      CompileCorrectWithinFor S Q unit steps (updPc pc (decClock s1))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hr : s1.regs r with
  | word _ => simp only [hr, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | loc n1 n2 =>
    simp only [hr] at hev
    cases hpc : locToPc n1 n2 s1.code with
    | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
    | some pc =>
      simp only [hpc] at hev
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, -, -, -, -, c45, -⟩ := id hrel
      have hreg : t1.regs r = p + BitVec.ofNat width (posVal pc 0 code2) := by
        have := c30 r
        rw [hr] at this
        simp only [wordLocVal, c28 n1 n2 pc hpc, Option.some.injEq] at this
        exact this.symm
      obtain ⟨bytes', len', hok, hmem, hpos, hdis, hbl⟩ :=
        fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
      simp only [lineOk, cbwToAsmHOL] at hok
      have hal := stateRel_aligned_target hrel (encoderCorrect_of_within hec) pc
      obtain ⟨l, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hfit _ bytes' hmem hok.1 hok.2.2 hdis
        (by simp [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal, ht1f])
      have htrel := (hl 0).2.2.1
      simp only [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal,
        Bool.not_true, Bool.false_or, ht1f] at htrel
      have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
        (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
          t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
      exact compileCorrect_step (s1' := LabSem.updPc pc (decClock s1)) ht hec hfit hclock
        (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
        (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl) le_rfl
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih n1 n2 pc hr hpc)

end SteppedFlapjack.LabToTargetSteps
