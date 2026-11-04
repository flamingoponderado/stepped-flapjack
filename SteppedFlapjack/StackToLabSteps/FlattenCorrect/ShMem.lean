import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Leaves
import Flapjack.Compiler.Backend.Semantics.StackSem.ShMem
import Flapjack.Pancake.CrepToLoop.Proofs.WriteBytearrayMemRel
import Flapjack.Pancake.Semantics.ByteAlignBridge

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/ShMem.lean`
(stepped-flapjack#2, phase C1): the `ShMemOp` case for `FlattenPropWithin`. The
flattened code is one LabSem shared-memory instruction, which takes one tick
when it returns and none on a final outcome; `shMemLoadSim` and `shMemStoreSim`
conclude `FlattenConclWithin`. Otherwise the statements and proofs follow the
original. -/

/-! `flatten_correct` case `ShMemOp` (`stack_to_labProofScript.sml:2520-2643`):
a StackSem shared-memory operation is simulated by the LabSem shared-memory
FFI step. StackSem renders HOL `word_to_bytes`/`word_of_bytes` through the
panSem byte helpers and LabSem through the wordSem ones; the two agree. -/

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

/-- The panSem and wordSem renderings of HOL `get_byte` agree. -/
theorem panGetByte_eq_getByteHOL8 {width : Nat} [NeZero width] (a w : BitVec width) :
    BitVec.ofNat 8 (panGetByteHOL a w false).toNat = getByteHOL8 a w false := by
  apply BitVec.eq_of_toNat_eq
  simp [panGetByteHOL, getByteHOL8, byteIndexHOL, Nat.shiftRight_eq_div_pow,
    pow256_eq_two_pow_mul]

/-- The panSem and LabSem renderings of HOL `word_to_bytes w F` agree. -/
theorem panWordToBytes_eq_shared {width : Nat} [NeZero width] (w : BitVec width) :
    panWordToBytesHOL w false = sharedMemoryWordBytes w := by
  simp only [panWordToBytesHOL, sharedMemoryWordBytes]
  congr 1
  funext i
  exact panGetByte_eq_getByteHOL8 _ _

/-- The panSem and wordSem renderings of HOL `word_of_bytes` agree. -/
theorem panWordOfBytes_eq_wordOfBytesHOL8 {width : Nat} [NeZero width] (be : Bool) :
    ∀ (a : BitVec width) (bs : List (BitVec 8)),
      panWordOfBytesHOL be a bs = wordOfBytesHOL8 be a bs := by
  intro a bs
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [panWordOfBytesHOL, wordOfBytesHOL8, ih]
    exact panSetByteHOL_eq_setByteHOL8 _ _ _ _

section
variable {width : Nat} [NeZero width] {C F : Type}

/-- The state relation after a returning shared-memory FFI step, whose
StackSem side optionally updates a register. -/
theorem stateRelShMemRet {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    (f : HolFfiState F) (pc : Nat) (upd : Option (Nat × WordLocW width)) :
    stateRel
      { StackSemStateOps.decClock s with
        regs := match upd with
          | none => s.regs
          | some (reg, v) => s.regs.updateEq (reg, v)
        ffi := f }
      { t with
        ffi := f
        regs := match upd with
          | none => t.regs
          | some (reg, v) => fun r => if r = reg then v else t.regs r
        pc := pc
        clock := t.clock - 1
        ioRegs := holShiftSeq 1 t.ioRegs
        ioFpRegs := holShiftSeq 1 t.ioFpRegs } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, _, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  refine ⟨?_, h2, h3, h4, h5, h6, rfl, by simp [StackSemStateOps.decClock, h8], h9, h10, h11,
    h12, h13, h14, h15, h16, h17, fun k i n hk => h18 k i (n + 1) hk, h19, h20, h21, h22, h23,
    h24, h25, h26, h27, h28, h29⟩
  intro r v hv
  cases upd with
  | none => exact h1 r v hv
  | some p =>
    obtain ⟨reg, w⟩ := p
    simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL] at hv ⊢
    split_ifs at hv ⊢ with e
    · cases hv; rfl
    · exact h1 r v hv

/-- One LabSem step of a fetched shared-memory line whose operation succeeds. -/
theorem evaluateShareMemStep {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {op : HolMemop} {reg : Nat} {address : HolAddr width} {bs : List (BitVec 8)} {k : Nat}
    {res : HolFfiResult F} {t' : Flapjack.Compiler.Backend.LabSem.State width C F}
    (hclk : t.clock ≠ 0)
    (fetch : asmFetchAux t.pc t.code = some (.asm (.shareMem op reg address) bs k))
    (hsh : shareMemOp op reg address t = some (res, t')) :
    evaluate t = match (generalizing := false) res with
      | .final outcome => (.halt (.ffiOutcome outcome), t')
      | .ret _ _ => evaluate { t' with
          ioRegs := holShiftSeq 1 t'.ioRegs
          ioFpRegs := holShiftSeq 1 t'.ioFpRegs } := by
  rw [evaluate]
  simp only [hclk, if_false, asmFetch, fetch]
  split
  · rename_i h; rw [hsh] at h; cases h
  · rename_i outcome next h; rw [hsh] at h; cases h; rfl
  · rename_i ffi bytes next _ h; rw [hsh] at h; cases h; rfl

theorem relShMdomain {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    t.sharedMemDomain = s.shMdomain := rel.2.2.2.2.1

theorem relShAligned {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    {x : BitVec width} (h : s.shMdomain x = true) : x.toNat % (width / 8) = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, align, _⟩ := rel
  exact align x h

omit [NeZero width] in
theorem sharedBytesTakeOne (v : BitVec width) (h : 0 < width / 8) :
    (sharedMemoryWordBytes v).take 1 = [getByteHOL8 0 v false] := by
  obtain ⟨m, hm⟩ : ∃ m, width / 8 = m + 1 := ⟨width / 8 - 1, by omega⟩
  simp [sharedMemoryWordBytes, hm, List.range_succ_eq_map]

/-- Simulation of a successful-dispatch shared-memory load of size `k`. -/
theorem shMemLoadSim {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemLoad reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedRead)
        [BitVec.ofNat 8 k] (panWordToBytesHOL addr false) with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi newBytes => (none, { StackSemStateOps.decClock s1 with
          regs := (StackSemStateOps.decClock s1).regs.updateEq
            (reg, .word (panWordOfBytesHOL false 0 newBytes))
          ffi := newFfi })) = (r, s2)) :
    FlattenConclWithin (.shMemOp op reg (.addr a w) : HolProg width) s1 t r s2 n l cs bs t1 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemLoad reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
          (sharedMemoryWordBytes addr) with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemLoad]
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true]
    cases callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
      (sharedMemoryWordBytes addr) <;> rfl
  rw [panWordToBytes_eq_shared,
    show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with clock := t1.clock + 0 }, leafBound rfl (by simp), ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with
        ffi := ffi'
        regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs },
      leafBound rfl (by simp only [flattenStepFactor]; omega), fun ck1 => ?_, rfl, rfl, rfl, rfl,
          rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with
          clock := t1.clock + 0 + ck1 - 1
          ffi := ffi'
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1)
        (some (reg, .word (wordOfBytesHOL8 false 0 bytes)))
      simpa [panWordOfBytes_eq_wordOfBytesHOL8, StackSemStateOps.decClock] using this

/-- Simulation of a successful-dispatch shared-memory store of size `k`. -/
theorem shMemStoreSim {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr v : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {payload : List (BitVec 8)}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hv : t1.regs reg = .word v)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemStore reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hpay : payload = (if k = 0 then sharedMemoryWordBytes v
      else (sharedMemoryWordBytes v).take k) ++ sharedMemoryWordBytes addr)
    (hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 k] payload with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi _ => (none, { StackSemStateOps.decClock s1 with ffi := newFfi })) =
        (r, s2)) :
    FlattenConclWithin (.shMemOp op reg (.addr a w) : HolProg width) s1 t r s2 n l cs bs t1 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemStore reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemStore]
    rw [show ({ t1 with clock := c } : Flapjack.Compiler.Backend.LabSem.State width C F).regs reg
      = .word v from hv]
    simp only
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true, ← hpay]
    cases callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload <;> rfl
  rw [show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with clock := t1.clock + 0 }, leafBound rfl (by simp), ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, { t1 with
        ffi := ffi'
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs },
      leafBound rfl (by simp only [flattenStepFactor]; omega), fun ck1 => ?_, rfl, rfl, rfl, rfl,
          rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with clock := t1.clock + 0 + ck1 - 1, ffi := ffi', pc := t1.pc + 1 })
        (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1) none
      simpa [StackSemStateOps.decClock] using this

/-- `ShMemOp` case. -/
theorem flattenCorrectShMemOp (s1 : StackSemStateFiniteExact width C F) (op : HolMemop)
    (reg a : Nat) (w : BitVec width) :
    FlattenPropWithin (.shMemOp op reg (.addr a w) : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_shMemOp] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have clk := relClock rel
  have ffiEq := relFfi rel
  split at ev
  · rename_i addr hexp
    have haddr : addrValue (.addr a w) t1 = some addr := InstCorrect.addrOfWordExp rel hexp
    split_ifs at ev with h0
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, t1, by simp, fun ck1 => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_,
          ?_⟩
      · simp [StackSemStateOps.emptyEnv, ffiEq]
      · omega
    · have cnz : t1.clock ≠ 0 := by omega
      have hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length = 1 := by
        simp [flattenHOL, appListAppendList, isLabelHOL]
      have good : goodDimindex width := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, g⟩ := rel
        exact g
      have pos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
      have err : ∀ {x : StackSemStateFiniteExact width C F},
          (some StackSemResult.error, x) = (r, s2) → False := fun e => by
        simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
      cases op
      case load =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim (k := 0) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom,
                relShAligned rel dom]) hlen ev
        · exact (err ev).elim
      case load8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoadByte] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim (k := 1) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad16] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim (k := 2) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad32] at ev
        split_ifs at ev with dom
        · exact shMemLoadSim (k := 4) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case store =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim (k := 0) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain
                  rel, dom, relShAligned rel dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStoreByte] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim (k := 1) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain
                  rel, dom])
              (by simp [panWordToBytes_eq_shared, sharedBytesTakeOne v pos]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore16] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim (k := 2) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain
                  rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore32] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSim (k := 4) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain
                  rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

end

end SteppedFlapjack.StackToLabSteps
