import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Step
import Flapjack.Compiler.Backend.LabToTarget.WordCmp

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Control.lean`
(stepped-flapjack#2, phase B): the `Jump`, `JumpCmp`, `Call`, `LocValue` and
`Halt` cases for `CompileCorrectWithinFor`. The simulated line takes `l` ticks
with `unit * l` at most its byte length, which is at most `maxLineBytes code2`.
A halting run takes these `l` ticks beyond the source clock. The `@[hol]`
attributes are dropped. Otherwise the statements and proofs follow the
original. -/

/-! Control-transfer cases of the original `compile_correct`
(lab_to_targetProofScript.sml:7967-8290, 9282-9351): `Jump`, `JumpCmp`,
`Call`, `LocValue` and `Halt`. Each case keeps every hypothesis of the
original theorem; recursive cases additionally take exactly the source
induction hypothesis for the state `evaluate` continues with. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- A source label's resolved position is its recorded target offset. -/
theorem findPos_of_getPcValue {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) (jt : Lab) (pc : Nat)
    (hpc : getPcValue jt s1 = some pc) :
    findPos jt labs = posVal pc 0 code2 ∧ getLabel (.jump jt : AsmWithLab HolCmp
      (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString) = jt := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c28, -⟩ := hrel
  rcases jt with ⟨l1, l2⟩
  exact ⟨labLookup_implies_findPos l1 l2 labs _ (c28 l1 l2 pc hpc), rfl⟩

theorem compileCorrect_jump {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (jt : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.jump jt) w bytes n))
    (ih : ∀ pc, getPcValue jt s1 = some pc →
      CompileCorrectWithinFor S Q unit steps (updPc pc (decClock s1))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hpc : getPcValue jt s1 with
  | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some pc =>
    simp only [hpc] at hev
    obtain ⟨hfind, -⟩ := findPos_of_getPcValue hrel jt pc hpc
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis, hbl⟩ := fetchedLabAsmLine hrel hfetch
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inl ⟨jt, rfl⟩) hok
    simp only [getLabel, labInst, hfind] at hv
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
    obtain ⟨l, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hfit _ bytes' hmem hv.1 hv.2.2 hdis
      (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
    have htrel := (hl 0).2.2.1
    have hnewpc : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
        BitVec.ofNat width (posVal s1.pc 0 code2)) = p + BitVec.ofNat width (posVal pc 0 code2) := by
      rw [htpc]; ring
    simp only [asmUpd, jumpToOffset, AsmSem.updPc, hnewpc] at htrel
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
      (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
        t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
    exact compileCorrect_step (s1' := LabSem.updPc pc (decClock s1)) ht hec hfit hclock
      (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
      (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl) le_rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih pc hpc)

theorem compileCorrect_jumpCmp {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (cmp : HolCmp) (rr : Nat) (ri : HolRegImm width)
    (jt : Lab) (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.jumpCmp cmp rr ri jt) w bytes n))
    (ihFalse : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some false →
      CompileCorrectWithinFor S Q unit steps (incPc (decClock s1)))
    (ihTrue : ∀ pc, wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) = some true →
      getPcValue jt s1 = some pc →
        CompileCorrectWithinFor S Q unit steps (updPc pc (decClock s1))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨w', bytes', len', hok, hmem, hpos, hdis, hbl⟩ := fetchedLabAsmLine hrel hfetch
  have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inl ⟨cmp, rr, ri, jt, rfl⟩)) hok
  simp only [getLabel, labInst] at hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  cases hc : wordSemWordCmp cmp (s1.regs rr) (LabSem.regImm ri s1) with
  | none => simp only [hc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some b =>
    have htc := wordCmp_lemma mc code2 labs p s1 t1 ms1 cmp rr ri b ⟨hrel, hc⟩
    cases b with
    | false =>
      simp only [hc] at hev
      obtain ⟨l, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hfit _ bytes' hmem hv.1 hv.2.2 hdis
        (by simp [asmUpd, ← htc, AsmSem.updPc, ht1f]) (fun _ _ => by simp [asmUpd, ← htc, AsmSem.updPc])
        (by intro x h; cases h)
      have htrel := (hl 0).2.2.1
      have hnewpc : t1.pc + BitVec.ofNat width bytes'.length =
          p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) := by
        rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
      simp only [asmUpd, ← htc, Bool.false_eq_true, ↓reduceIte, AsmSem.updPc, hnewpc] at htrel
      have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
        (stateRel_frame hrel s1.regs s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) t1.regs
          t1.fpRegs t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
      exact compileCorrect_step (s1' := incPc (decClock s1)) ht hec hfit hclock
        (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
        (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl) le_rfl
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ihFalse hc)
    | true =>
      simp only [hc] at hev
      cases hpc : getPcValue jt s1 with
      | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
      | some pc =>
        simp only [hpc] at hev
        obtain ⟨hfind, -⟩ := findPos_of_getPcValue hrel jt pc hpc
        simp only [hfind] at hv
        obtain ⟨l, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hfit _ bytes' hmem hv.1 hv.2.2 hdis
          (by simp [asmUpd, ← htc, jumpToOffset, AsmSem.updPc, ht1f])
        have htrel := (hl 0).2.2.1
        have hnewpc : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
            BitVec.ofNat width (posVal s1.pc 0 code2)) =
            p + BitVec.ofNat width (posVal pc 0 code2) := by
          rw [htpc]; ring
        simp only [asmUpd, ← htc, ↓reduceIte, jumpToOffset, AsmSem.updPc, hnewpc] at htrel
        have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
          (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
            t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
        exact compileCorrect_step (s1' := LabSem.updPc pc (decClock s1)) ht hec hfit hclock
          (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
          (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl) le_rfl
          ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ihTrue pc hc hpc)

/-- The source `Call` case: a related source state never fetches `Call`
(`line_ok` rejects it), so the original proof closes it from
`IMP_bytes_in_memory_Call`; its induction hypothesis is unused. -/
theorem compileCorrect_call {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (lab : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (_hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.call lab) w bytes n))
    (_ih : ∀ pc loc, getPcValue lab s1 = some pc → getRetLoc s1 = some loc →
      CompileCorrectWithinFor S Q unit steps (updPc pc (decClock (updReg s1.linkReg loc s1)))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, -, -, -, -, hrel⟩
  obtain ⟨w', bytes', len', hok, -⟩ := fetchedLabAsmLine hrel hfetch
  simp [lineOk] at hok

theorem compileCorrect_locValue {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (reg : Nat) (lab : Lab) (w : BitVec width)
    (bytes : List (BitVec 8)) (n : Nat) (hclock : s1.clock ≠ 0)
    (hfetch : asmFetch s1 = some (.labAsm (.locValue reg lab) w bytes n))
    (ih : getPcValue lab s1 ≠ none →
      CompileCorrectWithinFor S Q unit steps (incPc (decClock (updReg reg (labToLoc lab) s1)))) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hpc : getPcValue lab s1 with
  | none => simp only [hpc, ↓reduceIte, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | some pc =>
    simp only [hpc, reduceCtorEq, ↓reduceIte] at hev
    rcases lab with ⟨l1, l2⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
    have hlook := c28 l1 l2 pc hpc
    have hfind := labLookup_implies_findPos l1 l2 labs _ hlook
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis, hbl⟩ := fetchedLabAsmLine hrel hfetch
    have hv := lineOk_labelTarget _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨reg, .lab l1 l2, rfl⟩)) hok
    simp only [getLabel, labInst, hfind] at hv
    obtain ⟨l, ms2, hl⟩ := stepNopOfLine s1.ffi hrel hec hfit _ bytes' hmem hv.1 hv.2.2 hdis
      (by simp [asmUpd, AsmSem.updPc, AsmSem.updReg, ht1f])
      (fun _ _ => by simp [asmUpd, AsmSem.updPc, AsmSem.updReg]) (by intro x h; cases h)
    have htrel := (hl 0).2.2.1
    have hnewpc : t1.pc + BitVec.ofNat width bytes'.length =
        p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) := by
      rw [htpc, hpos, BitVec.ofNat_add, BitVec.add_assoc]
    have hval : t1.pc + (BitVec.ofNat width (posVal pc 0 code2) -
        BitVec.ofNat width (posVal s1.pc 0 code2)) = p + BitVec.ofNat width (posVal pc 0 code2) := by
      rw [htpc]; ring
    simp only [asmUpd, AsmSem.updPc, AsmSem.updReg, hnewpc, hval] at htrel
    have hregs : ∀ r, wordLocVal p labs
        ((fun key => if key = reg then labToLoc (.lab l1 l2) else s1.regs key) r) =
        some ((fun r' => if r' = reg then p + BitVec.ofNat width (posVal pc 0 code2)
          else t1.regs r') r) := by
      intro r
      by_cases hr : r = reg
      · simp [hr, labToLoc, wordLocVal, hlook]
      · simp only [hr, ↓reduceIte]; exact c30 r
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
      (stateRel_frame hrel _ s1.fpRegs s1.memory (s1.pc + 1) (s1.clock - 1) _ t1.fpRegs
        t1.mem _ htrel hregs c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
    exact compileCorrect_step (s1' := incPc (decClock (updReg reg (labToLoc (.lab l1 l2)) s1)))
      ht hec hfit hclock (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2.1
      (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl) le_rfl
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih (by simp [hpc]))

theorem compileCorrect_halt {width : Nat} [NeZero width] {S Q F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : LabSem.State width Config F) (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.labAsm .halt w bytes n)) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨-, -, -, c4, -, c6, c7, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c25, -,
    -, -, -, c30, -, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  cases hv : s1.regs s1.ptrReg with
  | loc _ _ => simp only [hv, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | word v =>
    simp only [hv] at hev
    obtain ⟨rfl, hs2⟩ : res = .halt (if v = 0 then .success else .resourceLimitHit) ∧
        s2 = s1 := by
      split at hev <;> simp_all
    rw [hs2]
    obtain ⟨w', bytes', len', hok, hmem, hpos, hdis, hbl⟩ := fetchedLabAsmLine hrel hfetch
    simp only [lineOk] at hok
    obtain ⟨l, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hfit _ bytes' hmem hok.1 hok.2.2 hdis
      (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
    obtain ⟨-, hgpc, -, hgreg, -⟩ := (hl 0).2.2.1
    have hhalt : mc.target.getPc ms2 = mc.haltPc := by
      rw [hgpc, ← c25]
      simp only [asmUpd, jumpToOffset, AsmSem.updPc, htpc, BitVec.ofNat_add]
      ring
    have hptr : mc.target.getReg ms2 mc.ptrReg = v := by
      have hok6 := c6
      simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hok6
      rw [hgreg _ (by rw [c7]; exact hok6), c7]
      simp only [asmUpd, jumpToOffset, AsmSem.updPc]
      exact wordLocVal_word_target (c30 _) hv
    refine ⟨l, ms2, tick_last_bound hclock (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl),
      ?_⟩
    rw [(hl s1.clock).1]
    obtain ⟨k, hk⟩ : ∃ k, s1.clock = k + 1 := ⟨s1.clock - 1, by omega⟩
    rw [hk, evaluateTargetHOL]
    have hnp : ¬ ((shiftInterfer l mc).progAddresses ((shiftInterfer l mc).target.getPc ms2) ∧
        (shiftInterfer l mc).target.getPc ms2 ∉ (shiftInterfer l mc).ffiEntryPcs) := by
      intro h; exact c4 (by simpa [shiftInterfer, hhalt] using h.1)
    simp only [hnp, ↓reduceIte]
    simp [shiftInterfer, hhalt, hptr]

end SteppedFlapjack.LabToTargetSteps
