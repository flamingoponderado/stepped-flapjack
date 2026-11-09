import SteppedFlapjack.StackAllocSteps.GcMoveCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveList

/-! Quantitative correctness of the simple collector object-list loop. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst)
open Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend
set_option maxHeartbeats 2000000

/-- The loop needs at most one bounded object move and one tick per entry. -/
theorem gcMoveListBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (n : Nat) (a i pa old a1 i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGcMoveList conf (a, BitVec.ofNat width n, i, pa, old, s.memory, s.mdomain) =
        (a1, i1, pa1, m1, true) →
      n < 2 ^ width →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      s.regs.lookup 7 = some (.word (BitVec.ofNat width n)) → s.regs.lookup 8 = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6, ck ≤ n * (2 ^ width + 1) ∧
        evaluate (wordGcMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  intro n
  induction n with
  | zero =>
      intro a i pa old a1 i1 pa1 m1 s hm _ _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8
      rw [show BitVec.ofNat width 0 = 0#width from rfl, wordGcMoveList_zero] at hm
      simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hm
      obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
      obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
      obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
      obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
      refine ⟨0, r0, r1, r2, r5, r6, by simp, ?_⟩
      rw [wordGcMoveListCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
      simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h7]
      simp [StackSemStateOps.getVarImm, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
        StackSemControl.exitLoop]
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
      by_cases k0 : k = 0
      · subst k0; simp [hr0]
      by_cases k1 : k = 1
      · subst k1; simp [hr1]
      by_cases k2 : k = 2
      · subst k2; simp [hr2]
      by_cases k3 : k = 3
      · subst k3; simp [h3]
      by_cases k4 : k = 4
      · subst k4; simp [h4]
      by_cases k5 : k = 5
      · subst k5; simp [hr5]
      by_cases k6 : k = 6
      · subst k6; simp [hr6]
      by_cases k7 : k = 7
      · subst k7; simp [h7]
      by_cases k8 : k = 8
      · subst k8; simp [h8]
      simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  | succ n ih =>
      intro a i pa old a1 i1 pa1 m1 s hm hlt hcurr huse h0 h1 h2 h3 h4 h5 h6 h7 h8
      have hne : BitVec.ofNat width (n + 1) ≠ 0 := by
        intro h
        have := congrArg BitVec.toNat h
        simp [Nat.mod_eq_of_lt hlt] at this
      have hpred : BitVec.ofNat width (n + 1) - 1 = BitVec.ofNat width n := by
        rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
      rw [wordGcMoveList_of_ne conf hne, hpred] at hm
      simp only at hm
      generalize hmv : wordGcMove conf (s.memory a, i, pa, old, s.memory, s.mdomain) = R1 at hm
      obtain ⟨w1, i1', pa1', m1', c1⟩ := R1
      simp only at hm
      generalize hrec : wordGcMoveList conf (a + wordSemBytesInWord, BitVec.ofNat width n, i1',
        pa1', old, gcUpdate a w1 m1', s.mdomain) = R2 at hm
      obtain ⟨a2, i2, pa2, m2, c2⟩ := R2
      simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
      obtain ⟨rfl, rfl, rfl, rfl, hda, hc1, hc2⟩ := hm
      subst hc1 hc2
      -- the state entering `word_gc_move_code`
      let SB : StackSemStateFiniteExact width C F :=
        setVar 7 (.word (BitVec.ofNat width n)) (setVar 5 (s.memory a) s)
      obtain ⟨ck, r0, r1, r2, r6, hckBound, hgc⟩ := gcMoveBoundedClock (s := SB)
        ⟨hmv, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl,
          by simpa [SB, setVar, FUPDATE_HOL] using h0, by simpa [SB, setVar, FUPDATE_HOL] using h1,
          by simpa [SB, setVar, FUPDATE_HOL] using h2, by simp [SB, getVar, setVar, FUPDATE_HOL, h3],
          by simp [SB, getVar, setVar, FUPDATE_HOL, h4], by simp [SB, getVar, setVar, FUPDATE_HOL],
          by simpa [SB, setVar, FUPDATE_HOL] using h6⟩
      -- the state the next iteration starts from
      let t : StackSemStateFiniteExact width C F :=
        setVar 8 (.word (a + wordSemBytesInWord))
          { SB with
            memory := gcUpdate a w1 m1'
            regs := SB.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1'),
              (4, .word i1'), (5, w1), (6, r6)] }
      obtain ⟨ck', r0', r1', r2', r5', r6', hckBound', hr⟩ := ih (a + wordSemBytesInWord) i1' pa1' old
        a2 i2 pa2 m2 t hrec (by omega) hcurr huse
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
        (by simp [t, SB, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq,
          FUPDATE_LIST_HOL])
        (by simp [t, setVar, FUPDATE_HOL])
      refine ⟨ck + ck' + 1, r0', r1', r2', r5', r6', ?_, ?_⟩
      · rw [Nat.add_mul]; simp only [Nat.one_mul]; omega
      ·
         -- `word_gc_move_code_thm` run with the `ck' + 1` clock the rest of the loop needs
        have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hgc, by simp⟩
        have hsb : setVar 7 (.word (BitVec.ofNat width (n + 1) - 1))
            (setVar 5 (s.memory a) { s with clock := s.clock + (ck + ck' + 1) }) =
            { { SB with clock := SB.clock + ck } with
              clock := { SB with clock := SB.clock + ck }.clock + (ck' + 1) } := by
          simp only [SB, setVar, hpred]
          congr 1
          omega
        have h5c : ({ SB with
              memory := m1'
              regs := SB.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1'),
                (4, .word i1'), (5, w1), (6, r6)] } : StackSemStateFiniteExact width C F).regs.lookup 5 =
            some w1 := by
          simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL]
        have h8c : ({ SB with
              memory := m1'
              regs := SB.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1'),
                (4, .word i1'), (5, w1), (6, r6)] } : StackSemStateFiniteExact width C F).regs.lookup 8 =
            some (.word a) := by
          simp [SB, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, h8]
        have hbody : evaluate (.seq (loadInst 5 8) (.seq (sub1Inst 7) (.seq (wordGcMoveCode conf)
            (.seq (storeInst 5 8) (addBytesInWordInst 8)))),
            { s with clock := s.clock + (ck + ck' + 1) }) =
            (none, { t with clock := t.clock + (ck' + 1) }) := by
          rw [evaluate_seq_none _ _ _ _
              (loadInst_eval { s with clock := s.clock + (ck + ck' + 1) } 5 8 a h8 hda) (by simp [setVar]),
            evaluate_seq_none _ _ _ _
              (sub1Inst_eval (setVar 5 (s.memory a) { s with clock := s.clock + (ck + ck' + 1) }) 7
                (BitVec.ofNat width (n + 1))
                (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h7])) (by simp [setVar]),
            hsb, evaluate_seq_none _ _ _ _ hadd (by simp [SB, setVar]),
            evaluate_seq_none _ _ _ _ (storeInst_eval _ 5 8 a w1 ?_ ?_ ?_) (by simp),
            addBytesInWordInst_eval _ 8 a ?_]
          · rfl
          · exact h8c
          · exact h5c
          · exact h8c
          · exact hda
        rw [wordGcMoveListCode_eq, evaluate_loop, evaluate_ite]
        simp only [getVar, HolRegImm.toWordRegImm, h7, StackSemStateOps.getVarImm, wordSemWordCmp,
          wordCmpHOL]
        have hcmp : (!(BitVec.ofNat width (n + 1) == 0)) = true := by simpa using hne
        simp only [hcmp]
        rw [hbody]
        have htc : t.clock = s.clock := rfl
        have hmin : min (s.clock + (ck + ck' + 1)) (t.clock + (ck' + 1)) = t.clock + (ck' + 1) := by
          omega
        have hck : t.clock + (ck' + 1) ≠ 0 := by omega
        simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock, ← wordGcMoveListCode_eq]
        refine (congrArg (fun st => evaluate (wordGcMoveListCode conf, st)) ?_).trans (hr.trans ?_)
        · congr 1
        · simp only [t, SB, setVar, Prod.mk.injEq, true_and]
          congr 1
          apply regs_ext
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
          · subst k4; simp
          by_cases k5 : k = 5
          · subst k5; simp
          by_cases k6 : k = 6
          · subst k6; simp
          by_cases k7 : k = 7
          · subst k7; simp
          by_cases k8 : k = 8
          · subst k8; simp
          simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]

end SteppedFlapjack.StackAllocSteps
