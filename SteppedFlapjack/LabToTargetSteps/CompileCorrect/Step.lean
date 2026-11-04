import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Common
import Flapjack.Compiler.Backend.LabToTarget.BytesInMemoryFetch
import Flapjack.Compiler.Backend.LabToTarget.FfiEntryDisjoint
import Flapjack.Compiler.Backend.LabToTarget.InstFrame
import SteppedFlapjack.LabToTargetSteps.AsmStepEvaluate
import Flapjack.Compiler.Backend.LabToTarget.Interference
import SteppedFlapjack.LabToTargetSteps.NopSteps
import SteppedFlapjack.LabToTargetSteps.BytesInMemoryFetch

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Step.lean`
(stepped-flapjack#2, phase B). The step lemmas take
`encoderCorrectWithin mc.target steps` and `StepsFit unit steps mc.target`
instead of `encoderCorrect mc.target`, and add that the simulated line of
`bytes'` takes `l` ticks with `unit * l ≤ bytes'.length`. The fetched-line
lemmas add that the target line is at most `maxLineBytes code2` bytes long.
Otherwise the statements and proofs follow the original. -/

/-! Flapjack infrastructure shared by the `compile_correct` cases: the
leading instruction of a fetched, validly encoded target line is simulated by
`asm_step_IMP_evaluate_step_find_next` from the full `state_rel`. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- The two orientations of the original optional link-register guard agree. -/
theorem linkGuard_flip {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (s : AsmState width)
    (h : match c.linkReg with
      | none => True
      | some r => s.lr = r) :
    match c.linkReg with
    | some r => s.lr = r
    | none => True := by
  revert h; cases c.linkReg <;> exact id

/-- Simulate the leading instruction `instr` of a fetched line whose bytes
`bytes'` encode it with NOP padding. -/
theorem stepOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    {unit : Nat} {steps : HolAsm width → Nat}
    (hec : encoderCorrectWithin mc.target steps) (hfit : StepsFit unit steps mc.target)
    (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length)
      t1).failed) :
    ∃ l ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target
        (asmUpd instr (t1.pc + BitVec.ofNat width (mc.target.config.encode instr).length) t1)
        ms2 ∧
      l ≠ 0 ∧ unit * l ≤ bytes'.length := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, ht1f, -, htpc, -, c43, c44, c45, -⟩ := hrel
  obtain ⟨count, rfl⟩ := (encWithNop_iff _ _ _).mp henc
  have hlen : (mc.target.config.encode instr).length ≤
      (mc.target.config.encode instr ++
        (List.replicate count (mc.target.config.encode (.inst .skip))).flatten).length := by
    simp
  obtain ⟨l, ms2, hl⟩ := asmStepImpEvaluate mc steps t1 ms1 io instr (by
    refine ⟨hec, c3, ffiEntryPcsDisjoint_shorter mc t1 _ _ ⟨hdis, hlen⟩, c27, ?_, c1⟩
    refine ⟨?_, linkGuard_flip _ _ c43, c44, c45, rfl, hnf, hok⟩
    rw [htpc]
    exact bytesInMem_encWithNop _ _ _ _ _ _ _ henc hmem)
  exact ⟨l, ms2, fun k => ⟨(hl k).1, (hl k).2.1, (hl k).2.2.1, (hl k).2.2.2.1,
    le_trans (le_trans (Nat.mul_le_mul_left _ (hl k).2.2.2.2) (hfit.2 instr)) hlen⟩⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), given that the line's
bytes are still in the target memory after the instruction. -/
theorem stepNopOfLineMem {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    {unit : Nat} {steps : HolAsm width → Nat}
    (hec : encoderCorrectWithin mc.target steps) (hfit : StepsFit unit steps mc.target)
    (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hb2 : bytesInMemoryHOL t1.pc bytes'
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem t1.memDomain)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 ∧ unit * l ≤ bytes'.length := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  apply asmStepImpEvaluateStepNop mc unit steps t1 ms1 io instr _ bytes' hfit
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

/-- Simulate a whole NOP-padded line `bytes'` encoding the non-`Call`
instruction `instr` (`asm_step_IMP_evaluate_step_nop`), when the instruction
leaves memory unchanged outside the source memory domain. -/
theorem stepNopOfLine {width : Nat} [NeZero width] {S Q F σ : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (io : HolFfiState σ) (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    {unit : Nat} {steps : HolAsm width → Nat}
    (hec : encoderCorrectWithin mc.target steps) (hfit : StepsFit unit steps mc.target)
    (instr : HolAsm width) (bytes' : List (BitVec 8))
    (hmem : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem
      t1.memDomain (fun a => s1.memDomain a = true))
    (henc : encWithNop mc.target.config.encode instr bytes')
    (hok : asmOkExact instr mc.target.config = true)
    (hdis : ffiEntryPcsDisjoint mc t1 bytes'.length)
    (hnf : ¬ (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).failed)
    (hmemeq : ∀ a, ¬ s1.memDomain a = true →
      (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem a = t1.mem a)
    (hcall : ∀ x, instr ≠ .call x) :
    ∃ l ms2, ∀ k,
      evaluateTargetHOL mc io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l mc) io k ms2 ∧
      findNextInterference mc io (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) io k ms2 ∧
      targetStateRel mc.target (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1)
        ms2 ∧
      l ≠ 0 ∧ unit * l ≤ bytes'.length := by
  obtain ⟨c1, -, c3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    c27, -, -, -, -, -, -, -, -, -, -, -, -, -, htpc, -, c43, c44, c45, -⟩ := hrel
  have hb := bytesInMem_impliesMemory _ _ _ _ _ hmem
  rw [← htpc] at hb
  have hb2 := bytesInMem_impliesMemory_change _ t1.mem
    (asmUpd instr (t1.pc + BitVec.ofNat width bytes'.length) t1).mem _ bytes' _
    (fun a ha => (hmemeq a ha).symm) hmem
  rw [← htpc] at hb2
  apply asmStepImpEvaluateStepNop mc unit steps t1 ms1 io instr _ bytes' hfit
  refine ⟨hec, c3, hdis, c27, hb2, ?_, rfl, c1, hcall⟩
  exact ⟨hb, henc, c43, c44, c45, rfl, hnf, hok⟩

/-- The target line for a fetched source `LabAsm` instruction: same
instruction, valid at its position, its bytes in memory, the successor
position, and away from the FFI entry PCs. -/
theorem fetchedLabAsmLine {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    {a : AsmWithLab HolCmp (HolRegImm width) Flapjack.Basis.Pure.MlString.MlString}
    {w : BitVec width} {bytes : List (BitVec 8)} {n : Nat}
    (hfetch : asmFetch s1 = some (.labAsm a w bytes n)) :
    ∃ w' bytes' len',
      lineOk mc.target.config labs (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
        (posVal s1.pc 0 code2) (.labAsm a w' bytes' len') ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem t1.memDomain
        (fun x => s1.memDomain x = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length ∧
      ffiEntryPcsDisjoint mc t1 bytes'.length ∧ bytes'.length ≤ maxLineBytes code2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, c33, -, -, -, -, -, -, -, htpc, -, -, -, -, -, c47, -, c49, -, c51,
    -⟩ := id hrel
  obtain ⟨j, hmem, hok, hpos, hsim, hjm⟩ :=
    imp_bytesInMemory_state_mem mc labs _ s1 code2 p t1 _ ⟨c49, c47, c33, hfetch⟩
  cases j with
  | label => exact hsim.elim
  | asm => exact hsim.elim
  | labAsm a' w' bytes' len' =>
    simp only [lineSimilar] at hsim
    subst hsim
    refine ⟨w', bytes', len', hok, hmem, hpos, ?_, le_maxLineBytes hjm⟩
    exact imp_ffiEntryPcsDisjoint_labAsm s1 mc code2 labs _ a w bytes n p bytes' t1
      ⟨c49, c47, hfetch, c51, hmem, by rw [hpos]; simp [lineBytes, Nat.add_comm], htpc⟩

/-- The target line for a fetched source `Asm` line that is not a shared
memory access. -/
theorem fetchedAsmLine {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1)
    {b : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)} {bytes : List (BitVec 8)} {n : Nat}
    (hfetch : asmFetch s1 = some (.asm b bytes n)) (hb : ∀ op re a, b ≠ .shareMem op re a) :
    ∃ bytes' len',
      lineOk mc.target.config labs (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)))
        (posVal s1.pc 0 code2) (.asm b bytes' len') ∧
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes' t1.mem t1.memDomain
        (fun x => s1.memDomain x = true) ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + bytes'.length ∧
      ffiEntryPcsDisjoint mc t1 bytes'.length ∧ bytes'.length ≤ maxLineBytes code2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, c33, -, -, -, -, -, -, -, htpc, -, -, -, -, -, c47, -, c49, -, c51,
    -⟩ := id hrel
  obtain ⟨j, hmem, hok, hpos, hsim, hjm⟩ :=
    imp_bytesInMemory_state_mem mc labs _ s1 code2 p t1 _ ⟨c49, c47, c33, hfetch⟩
  cases j with
  | label => exact hsim.elim
  | labAsm => exact hsim.elim
  | asm b' bytes' len' =>
    simp only [lineSimilar] at hsim
    subst hsim
    refine ⟨bytes', len', hok, hmem, hpos, ?_, le_maxLineBytes hjm⟩
    exact imp_ffiEntryPcsDisjoint_asm s1 mc code2 labs _ b bytes n p bytes' t1
      ⟨c49, c47, hfetch, hb, c51, hmem, by rw [hpos]; simp [lineBytes, Nat.add_comm], htpc⟩

end SteppedFlapjack.LabToTargetSteps
