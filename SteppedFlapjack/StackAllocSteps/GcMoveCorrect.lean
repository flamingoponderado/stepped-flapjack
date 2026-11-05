import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMove

/-! Object-movement correctness with a proved upper bound on extra clock. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)
open Flapjack.Compiler.Backend.StackAlloc
set_option maxHeartbeats 2000000

/-- The original object-movement simulation needs at most `2^width` extra ticks. -/
theorem gcMoveBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    {w : WordLocW width} {i pa old : BitVec width} {m : BitVec width → WordLocW width}
    {dm : BitVec width → Bool} {w1 : WordLocW width} {i1 pa1 : BitVec width}
    {m1 : BitVec width → WordLocW width} {s : StackSemStateFiniteExact width C F} :
    wordGcMove conf (w, i, pa, old, m, dm) = (w1, i1, pa1, m1, true) ∧
      shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
      conf.lenSize ≠ 0 ∧
      (∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) ∧
      s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
      s.memory = m ∧ s.mdomain = dm ∧
      (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
      (s.regs.lookup 2).isSome = true ∧
      getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧ getVar 5 s = some w ∧
      (s.regs.lookup 6).isSome = true →
    ∃ ck r0 r1 r2 r6, ck ≤ 2 ^ width ∧ evaluate (wordGcMoveCode conf, { s with clock := s.clock + ck }) =
      (none, { s with
        memory := m1
        regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1), (4, .word i1),
          (5, w1), (6, r6)] }) := by
  rintro ⟨hmove, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
  obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
  have h3' : s.regs.lookup 3 = some (.word pa) := by simpa [getVar] using h3
  have h4' : s.regs.lookup 4 = some (.word i) := by simpa [getVar] using h4
  have h5' : s.regs.lookup 5 = some w := by simpa [getVar] using h5
  cases w with
  | loc l1 l2 =>
      simp only [wordGcMove, Prod.mk.injEq, decide_eq_true_eq] at hmove
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hmove
      refine ⟨0, r0, r1, r2, r6, Nat.zero_le _, ?_⟩
      rw [gcMove_skip_regs s r0 r1 r2 r6 _ _ _ hr0 hr1 hr2 h3' h4' h5' hr6]
      rw [wordGcMoveCode_eq, evaluate_ite]
      simp [getVar, h5', StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
        evaluate_skip]
  | word v =>
      by_cases hv : v &&& 1 = 0
      · simp only [wordGcMove, hv, if_true, Prod.mk.injEq] at hmove
        obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hmove
        refine ⟨0, r0, r1, r2, r6, Nat.zero_le _, ?_⟩
        rw [gcMove_skip_regs s r0 r1 r2 r6 _ _ _ hr0 hr1 hr2 h3' h4' h5' hr6]
        rw [wordGcMoveCode_eq, evaluate_ite]
        have hv' : AndOp.and v (1#width) = 0#width := hv
        simp [getVar, h5', StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
          wordCmpHOL, hv', evaluate_skip]
      · have hv0 : ¬ AndOp.and v (1#width) = 0#width := hv
        have hv' : (AndOp.and v (1#width) == 0#width) = false := by simpa using hv0
        have hsl_le : ¬ width ≤ shiftLength conf := by omega
        have hws_le : ¬ width ≤ wordShiftAmount width := by omega
        have h2_le : ¬ width ≤ 2 := by omega
        have hpow : width < 2 ^ width := Nat.lt_two_pow_self
        have hkm : (width - (smallShiftLength conf - 1) - 1) % 2 ^ width =
            width - (smallShiftLength conf - 1) - 1 :=
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
            (show width - (smallShiftLength conf - 1) - 1 ≤ width by omega) hpow)
        have hk_le : ¬ width ≤ width - (smallShiftLength conf - 1) - 1 := by omega
        have haddr : (v >>> shiftLength conf <<< wordShiftAmount width) + old =
            ptrToAddr conf old v := by
          rw [hshift, ptrToAddr, BitVec.add_comm]
        have hslm : shiftLength conf % 2 ^ width = shiftLength conf := Nat.mod_eq_of_lt (by omega)
        have hwsm : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
          Nat.mod_eq_of_lt (by omega)
        have h2m : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt (by omega)
        have hr1' := hr1
        have hcur : s.store.lookup (StackSemRegisterTransfers.storeOfSyntax .currHeap) =
            some (.word old) := hcurr
        simp only [wordGcMove, hv, if_false] at hmove
        by_cases hfwd : wordSemIsFwdPtr (s.memory (ptrToAddr conf old v)) = true
        · simp only [hfwd, if_true, Prod.mk.injEq] at hmove
          obtain ⟨rfl, rfl, rfl, rfl, hdm⟩ := hmove
          obtain ⟨x, hx, hx3⟩ := (is_fwd_ptr_iff _).1 hfwd
          have hx3a : AndOp.and x (3#width) = 0#width := hx3
          have hx3' : (AndOp.and x (3#width) == 0#width) = true := by simpa using hx3a
          refine ⟨0, .word (((v >>> shiftLength conf) <<< wordShiftAmount width) + old),
            .word ((x >>> 2) <<< shiftLength conf), r2, r6, Nat.zero_le _, ?_⟩
          rw [wordGcMoveCode_eq, evaluate_ite]
          simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
            wordCmpHOL, hv', listSeqHOL, evaluate_seq, evaluate_inst, evaluate_get, evaluate_ite,
            moveHOL, clearTopInst, orInst, loadInst, addInst, rightShiftInst, leftShiftInst,
            StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
            StackSemExpressions.assign, StackSemExpressions.wordExp, setVar, memLoad, wordOpHOL,
            wordOp, fixClock, huse, hcur, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h5',
            hslm, hwsm, h2m, wordShiftHOL, hsl_le, hws_le, h2_le, haddr, hdm, hx, hx3', hkm, hk_le]
          have hor : ∀ a b : BitVec width, OrOp.or a b = a ||| b := fun _ _ => rfl
          apply regs_ext
          intro k
          simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
            FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
          by_cases k0 : k = 0
          · subst k0; simp
          by_cases k1 : k = 1
          · subst k1; simp
          by_cases k2 : k = 2
          · subst k2; simp [hr2]
          by_cases k3 : k = 3
          · subst k3; simp [h3']
          by_cases k4 : k = 4
          · subst k4; simp [h4']
          by_cases k5 : k = 5
          · subst k5; simp [hor, updateAddr, select_lower_lemma, BitVec.or_comm]
          by_cases k6 : k = 6
          · subst k6; simp [hr6]
          simp [k0, k1, k2, k3, k4, k5, k6]
        · have hfwd' : wordSemIsFwdPtr (s.memory (ptrToAddr conf old v)) = false := by
            simpa using hfwd
          simp only [hfwd', Bool.false_eq_true, if_false] at hmove
          have hc := congrArg (fun t => t.2.2.2.2) hmove
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hdm, -, hisw⟩, -, hc1⟩ := hc
          obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
          have hx3 : ¬ x &&& 3 = 0 := by simpa [hx, wordSemIsFwdPtr] using hfwd'
          simp only [hx, wordSemTheWord, Prod.mk.injEq] at hmove hc1
          obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hmove
          have hx3a : ¬ AndOp.and x (3#width) = 0#width := hx3
          have hx3' : (AndOp.and x (3#width) == 0#width) = false := by simpa using hx3a
          have hlm : (width - conf.lenSize) % 2 ^ width = width - conf.lenSize :=
            Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (show width - conf.lenSize ≤ width by omega) hpow)
          have hl_le : ¬ width ≤ width - conf.lenSize := by omega
          have hdec : x >>> (width - conf.lenSize) = decodeLength conf x := rfl
          refine ⟨(decodeLength conf x + 1).toNat, .word (i <<< 2), .word (i <<< shiftLength conf),
            .word (ptrToAddr conf old v), .word (decodeLength conf x + 1),
            Nat.le_of_lt (BitVec.isLt _), ?_⟩
          rw [wordGcMoveCode_eq, evaluate_ite]
          simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp,
            wordCmpHOL, hv', listSeqHOL, evaluate_seq, evaluate_inst, evaluate_get, evaluate_ite,
            moveHOL, clearTopInst, orInst, loadInst, storeInst, addInst, subInst, add1Inst,
            rightShiftInst, leftShiftInst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
            StackSemExpressions.wordExp, setVar, memLoad, memStore, wordOpHOL, wordOp, fixClock,
            huse, hcur, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h5', hslm, hwsm, h2m,
            wordShiftHOL, hsl_le, hws_le, haddr, hdm, hx, hx3', hlm, hl_le, hdec]
          rw [memcpyCode_eval _ (decodeLength conf x + 1) (ptrToAddr conf old v) pa ?_ ?_ ?_ ?_ ?_ ?_]
          rotate_left
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, h3']
          · exact hc1
          · simp
          have hback : ptrToAddr conf old v + (decodeLength conf x + 1#width) * wordSemBytesInWord -
              (decodeLength conf x <<< wordShiftAmount width + 1#width <<< wordShiftAmount width) =
              ptrToAddr conf old v := by
            rw [hshift, hshift, ← BitVec.add_mul, BitVec.add_sub_cancel]
          simp [HolFiniteMapExact.lookup_updateEq, HolFiniteMapExact.lookup_updateListEq,
            FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL, hslm, hwsm, h2m, hsl_le, hws_le, h2_le, hdm,
            hkm, hk_le, h4', h5', hback]
          have hor : ∀ a b : BitVec width, OrOp.or a b = a ||| b := fun _ _ => rfl
          refine ⟨?_, ?_⟩
          · apply regs_ext
            intro k
            simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
              FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
            by_cases k0 : k = 0
            · subst k0; simp
            by_cases k1 : k = 1
            · subst k1; simp
            by_cases k2 : k = 2
            · subst k2; simp
            by_cases k3 : k = 3
            · subst k3; simp
            by_cases k4 : k = 4
            · subst k4; simp [BitVec.add_assoc]
            by_cases k5 : k = 5
            · subst k5; simp [hor, updateAddr, select_lower_lemma, BitVec.or_comm]
            by_cases k6 : k = 6
            · subst k6; simp
            simp [k0, k1, k2, k3, k4, k5, k6]
          · funext key
            simp [gcUpdate, eq_comm]


end SteppedFlapjack.StackAllocSteps
