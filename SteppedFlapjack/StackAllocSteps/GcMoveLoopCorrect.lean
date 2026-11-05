import SteppedFlapjack.StackAllocSteps.GcMoveListCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GcMoveLoop

/-! Bounded-clock correctness for the simple collector heap traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst)
set_option maxHeartbeats 2000000

/-- The object-list clock bound with a word-sized length. -/
theorem gcMoveListWordBoundedClock {width : Nat} [NeZero width] {C F : Type} :
    ∀ (l a : BitVec width) (s : StackSemStateFiniteExact width C F) (pa1 pa old : BitVec width)
      (m1 m : BitVec width → WordLocW width) (i1 i : BitVec width) (dm : BitVec width → Bool)
      (conf : Config) (a1 : BitVec width),
      wordGcMoveList conf (a, l, i, pa, old, m, dm) = (a1, i1, pa1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      getVar 7 s = some (.word l) ∧ getVar 8 s = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6, ck ≤ l.toNat * (2 ^ width + 1) ∧
        evaluate (wordGcMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  rintro l a s pa1 pa old m1 m i1 i dm conf a1
    ⟨hm, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, h0, h1, h2, h3, h4, h5⟩ h6 ⟨h7, h8⟩
  have hl : l = BitVec.ofNat width l.toNat := by simp
  rw [hl] at hm h7
  exact gcMoveListBoundedClock hsl hws hw2 hlen hshift l.toNat a i pa old a1 i1 pa1 m1 s hm
    l.isLt hcurr huse h0 h1 h2 (by simpa [getVar] using h3) (by simpa [getVar] using h4) h5 h6
    (by simpa [getVar] using h7) (by simpa [getVar] using h8)


/-- Successful traversal needs a bounded amount of extra clock per fuel unit. -/
theorem gcMoveLoopBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∀ (k : Nat) (pb i pa old : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGcMoveLoop k conf (pb, i, pa, old, s.memory, s.mdomain, c) = (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word pb) → c = true →
      ∃ ck r0 r1 r2 r5 r6 r7, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pb i pa old c i2 pa2 m2 s hm hcurr huse h0 h1 h2 h3 h4 h5 h6 h7 h8 hc
  rw [wordGcMoveLoop] at hm
  by_cases hp : pb = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, by simp, ?_⟩
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h3]
    simp [StackSemStateOps.getVarImm, getVar, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, h8]
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
    · subst k7; simp [hr7]
    by_cases k8 : k = 8
    · subst k8; simp [h8]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8]
  have hk : k ≠ 0 := by
    intro hk; subst hk; simp [hp] at hm
  simp only [hp, hk, if_false] at hm
  have hpb : (!(pa == pb)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory pb)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    have hc0 := wordGcMoveLoop_ok hm rfl
    simp only [Bool.and_eq_true] at hc0
    obtain ⟨-, hdm, hisw⟩ := hc0
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hm hb
    simp only [wordSemTheWord] at hm hb
    have hc1 := wordGcMoveLoop_ok hm rfl
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (pb + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, hprev, hr⟩ := ih (k - 1) (by omega) _ i pa old _ i2 pa2 m2 s5
      hm hcurr huse
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL]) hc1
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) +
        (2 ^ width * (2 ^ width + 1) + 1) =
        k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hbudget : ck + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by
      omega
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, hbudget, ?_⟩
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [gcMoveLoop_body_skip conf { s with clock := s.clock + (ck + 1) } pb x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGcMoveLoopCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveLoopCode conf, st)) ?_).trans (hr.trans ?_)
    · simp only [s5, setVar]
      congr 1
    · simp only [s5, setVar, Prod.mk.injEq, true_and]
      congr 1
      apply regs_ext
      intro k
      simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
        FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
      by_cases k7 : k = 7
      · subst k7; simp
      by_cases k8 : k = 8
      · subst k8; simp
      simp [k7, k8]
  · simp only [hb, Bool.false_eq_true, if_false] at hm
    generalize hl : wordGcMoveList conf (pb + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory pb)), i, pa, old, s.memory, s.mdomain) = R at hm
    obtain ⟨pb3, i1, pa1, m1, c1⟩ := R
    simp only at hm
    have hc0 := wordGcMoveLoop_ok hm rfl
    simp only [Bool.and_eq_true] at hc0
    obtain ⟨⟨-, hdm, hisw⟩, hc1⟩ := hc0
    subst hc1
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hm hb hl
    simp only [wordSemTheWord] at hm hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    have hc2 := wordGcMoveLoop_ok hm rfl
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, hinner, hL⟩ := gcMoveListWordBoundedClock (decodeLength conf x)
      (pb + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain conf pb3
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word pb3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, hprev, hr⟩ := ih (k - 1) (by omega) pb3 i1 pa1 old _ i2 pa2 m2 s6
      hm hcurr huse
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      hc2
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) +
        (2 ^ width * (2 ^ width + 1) + 1) =
        k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hlenBound : (decodeLength conf x).toNat * (2 ^ width + 1) ≤
        2 ^ width * (2 ^ width + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _))
    have hbudget : ck + ck' + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by
      omega
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, hbudget, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGcMoveLoopCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [gcMoveLoop_body_list conf { s with clock := s.clock + (ck + ck' + 1) } pb x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGcMoveLoopCode_eq]
    refine (congrArg (fun st => evaluate (wordGcMoveLoopCode conf, st)) ?_).trans (hr.trans ?_)
    · congr 1
    · simp only [s6, s5, setVar, Prod.mk.injEq, true_and]
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
