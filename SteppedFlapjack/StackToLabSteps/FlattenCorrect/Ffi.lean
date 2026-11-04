import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Leaves

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Ffi.lean`
(stepped-flapjack#2, phase C1): the `FFI` case for `FlattenPropWithin`. The
flattened code runs two LabSem instructions, the `LocValue` of the return label
and `CallFFI`; a final outcome halts at `CallFFI` after one tick. Otherwise the
statements and proofs follow the original. -/

/-! `flatten_correct` case `FFI` (`stack_to_labProofScript.sml:2660-2727`):
the flattened `LocValue` of the return label followed by `CallFFI` simulates a
StackSem foreign-function call. -/

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

section
variable {width : Nat} [NeZero width] {C F : Type}

/-- The state relation after a returning external call. -/
theorem stateRelFfiRet {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    (f : Basis.Pure.MlString.MlString) (ret : Nat) (hret : ret = t.linkReg) (loc : WordLocW width)
    (m : BitVec width → WordLocW width) (newFfi : HolFfiState F) (pc : Nat) :
    stateRel
      { s with
        memory := m
        regs := StackSemStateOps.restrictIn s.regs s.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := newFfi }
      { t with
        memory := m
        ffi := newFfi
        ioRegs := holShiftSeq 1 t.ioRegs
        ioFpRegs := holShiftSeq 1 t.ioFpRegs
        regs := fun r => getRegValue (t.ioRegs 0 (.extCall f) r)
          ((fun x => if x = ret then loc else t.regs x) r) WordLocW.word
        fpRegs := fun r => t.ioFpRegs 0 r
        pc := pc } := by
  obtain ⟨h1, h2, _, h4, h5, h6, _, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  refine ⟨?_, ?_, rfl, h4, h5, h6, rfl, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    fun k i n hk => h18 k i (n + 1) hk, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩
  · intro r v hv
    simp only [StackSemStateOps.restrictIn] at hv
    split_ifs at hv with hs
    have hio := h18 r (.extCall f) 0 hs
    have hne : r ≠ ret := by
      rintro rfl; rw [hret] at hs; exact h17 hs
    simp only [hio, getRegValue, hne, if_false]
    exact h1 r v hv
  · intro r v hv
    simp [HolFiniteMapExact.empty] at hv

/-- `FFI` case. -/
theorem flattenCorrectFfi (s1 : StackSemStateFiniteExact width C F)
    (f : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
    FlattenPropWithin (.ffi f ptr len ptr2 len2 ret : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_ffi] at ev
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm (.callFFI f) 0 [] 0, .label n l 0] t1.code := by
    simpa [flattenHOL, appListAppendList] using inst
  simp only [isLabelHOL, Bool.false_eq_true, if_false, if_true,
    codeInstalled] at hinst
  obtain ⟨fetch0, fetch1, locL, -⟩ := hinst
  obtain ⟨-, -, hmem, hdom, -, hbe, hffiEq, hclk, -, -, -, hnf, d13, d14, d15, d16, -⟩ := id rel
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  · rename_i w w2 w3 w4 hlen hptr hlen2 hptr2
    have rlen := InstCorrect.regOfLookup rel hlen
    have rptr := InstCorrect.regOfLookup rel hptr
    have rlen2 := InstCorrect.regOfLookup rel hlen2
    have rptr2 := InstCorrect.regOfLookup rel hptr2
    split at ev
    · rename_i cfg bytes hcfg hbytes
      rw [← hmem, ← hdom, ← hbe] at hcfg hbytes
      -- the two LabSem steps from any clock `c + 2`
      have step : ∀ c, evaluate { t1 with clock := c + 2 } =
          match callFFIHOL t1.ffi (.extCall f) cfg bytes with
          | .final outcome => (.halt (.ffiOutcome outcome),
              incPc (decClock (updReg t1.linkReg (.loc n l) { t1 with clock := c + 2 })))
          | .ret newFfi returned => evaluate { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2
              clock := c } := by
        intro c
        rw [evaluate]
        simp only [show c + 2 ≠ 0 by omega, if_false, asmFetch, fetch0, getPcValue, locL,
          reduceCtorEq]
        rw [evaluate]
        simp only [incPc, decClock, updReg, labToLoc, show c + 2 - 1 ≠ 0 by omega, if_false,
          asmFetch, fetch1, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, if_true,
          rlen, rptr, rlen2, rptr2, hcfg, hbytes, locL]
        cases callFFIHOL t1.ffi (.extCall f) cfg bytes with
        | final o => rfl
        | ret newFfi returned =>
          simp only
          congr 1
      rw [← hffiEq] at ev
      split at ev
      · rename_i outcome hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, incPc (decClock (updReg t1.linkReg (.loc n l)
          { t1 with clock := t1.clock + 2 })),
          leafBound rfl (by simp [flattenStepFactor, incPc, decClock, updReg]), ?_, ?_⟩
        · rw [step, hffi]
        · simp [incPc, decClock, updReg, hffiEq]
      · rename_i newFfi returned hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2 }, leafBound rfl (by simp [flattenStepFactor]), fun ck1 => ?_, rfl,
                  rfl, rfl, rfl, rfl, List.prefix_refl _,
          ?_, ?_⟩
        · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1) + 2 by omega, step, hffi]
        · simp [flattenHOL, appListAppendList, isLabelHOL]
        · have := stateRelFfiRet rel f t1.linkReg rfl (.loc n l)
            (writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be) newFfi (t1.pc + 2)
          simpa [hmem, hdom, hbe] using this
    · exact (err ev).elim
  · exact (err ev).elim

end

end SteppedFlapjack.StackToLabSteps
