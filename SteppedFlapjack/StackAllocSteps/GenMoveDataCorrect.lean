import SteppedFlapjack.StackAllocSteps.GenMoveListCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveData
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveRefs
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveRefList

/-! Bounded-clock correctness for generational data and reference traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)
set_option maxHeartbeats 2000000

/-- Full generational object-list bound in the data interface. -/
theorem genGcMoveListWordBoundedClock {width : Nat} [NeZero width] {C F : Type} :
    ∀ (l a : BitVec width) (s : StackSemStateFiniteExact width C F) (pa1 pa old : BitVec width)
      (m1 m : BitVec width → WordLocW width) (i1 i : BitVec width) (dm : BitVec width → Bool)
      (conf : Config) (a1 ib ib1 pb pb1 : BitVec width),
      wordGenGcMoveList conf (a, l, i, pa, ib, pb, old, m, dm) =
          (a1, i1, pa1, ib1, pb1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      getVar 7 s = some (.word l) ∧ getVar 8 s = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6 t0 t1, ck ≤ l.toNat * (2 ^ width + 1) ∧
        evaluate (wordGenGcMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  rintro l a s pa1 pa old m1 m i1 i dm conf a1 ib ib1 pb pb1
    ⟨hm, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3, h0, h1, h2, h3,
      h4, h5⟩ h6 ⟨h7, h8⟩
  have hl : l = BitVec.ofNat width l.toNat := by simp
  rw [hl] at hm h7
  exact genGcMoveListBoundedClock hsl hws hw2 hlen hshift l.toNat a i pa ib pb old a1 i1 pa1 ib1
    pb1 m1 s hm l.isLt hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7) (by simpa [getVar] using h8)


/-- Partial generational object-list bound in the data interface. -/
theorem genGcPartialMoveListWordBoundedClock {width : Nat} [NeZero width] {C F : Type} :
    ∀ (l a : BitVec width) (s : StackSemStateFiniteExact width C F) (pa1 pa old : BitVec width)
      (m1 m : BitVec width → WordLocW width) (i1 i : BitVec width) (dm : BitVec width → Bool)
      (conf : Config) (a1 gs rs : BitVec width),
      wordGenGcPartialMoveList conf (a, l, i, pa, old, m, dm, gs, rs) =
          (a1, i1, pa1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ goodDimindex width ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      getVar 7 s = some (.word l) ∧ getVar 8 s = some (.word a) →
      ∃ ck r0 r1 r2 r5 r6, ck ≤ l.toNat * (2 ^ width + 1) ∧
        evaluate (wordGenGcPartialMoveListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, .word 0), (8, .word a1)] }) := by
  rintro l a s pa1 pa old m1 m i1 i dm conf a1 gs rs
    ⟨hm, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs, h0, h1, h2, h3, h4,
      h5⟩ h6 ⟨h7, h8⟩
  have hl : l = BitVec.ofNat width l.toNat := by simp
  rw [hl] at hm h7
  exact genGcPartialMoveListBoundedClock hsl hws hw2 hlen hg hshift l.toNat a i pa old a1 i1 pa1
    m1 s hm l.isLt hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7) (by simpa [getVar] using h8)


/-- Full generational data traversal has a fuel-based clock bound. -/
theorem genGcMoveDataBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveData conf k (ha, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa ib pb i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 h0 h1 h2 h3 h4 h5 h6 h7
    h8
  rw [wordGenGcMoveData] at hm
  by_cases hp : ha = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
    obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, t0, t1, Nat.zero_le _, ?_⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
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
  have hpb : (!(pa == ha)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory ha)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    generalize hrec : wordGenGcMoveData conf (k - 1) (ha + (decodeLength conf
      (wordSemTheWord (s.memory ha)) + 1) * wordSemBytesInWord, i, pa, ib, pb, old, s.memory,
      s.mdomain) = R at hm
    obtain ⟨i3, pa3, ib3, pb3, m3, c3⟩ := R
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hrec hb
    simp only [wordSemTheWord] at hrec hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, u0, u1, hprev, hr⟩ := ih (k - 1) (by omega) _ i pa ib pb i3 pa3
      ib3 pb3 m3 s5 hrec hcurr huse ht0 ht1 ht2 ht3
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL])
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hbudget : ck + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, u0, u1, hbudget, ?_⟩
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_skip conf _ { s with clock := s.clock + (ck + 1) } ha x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGenGcMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
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
    generalize hl : wordGenGcMoveList conf (ha + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, ib, pb, old, s.memory,
      s.mdomain) = R at hm
    obtain ⟨ha3, i1, pa1, ib1, pb1, m1, c1⟩ := R
    simp only at hm
    generalize hrec : wordGenGcMoveData conf (k - 1) (ha3, i1, pa1, ib1, pb1, old, m1,
      s.mdomain) = R2 at hm
    obtain ⟨i3, pa3, ib3, pb3, m3, c3⟩ := R2
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hb hl
    simp only [wordSemTheWord] at hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, g0, g1, hinner, hL⟩ := genGcMoveListWordBoundedClock
      (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
      conf ha3 ib ib1 pb pb1
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        store := s5.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb1),
          (.temp 3, .word ib1)]
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, u0, u1, hprev, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1 ib1 pb1
      i3 pa3 ib3 pb3 m3 s6 hrec
      (by simp [s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
        FUPDATE_HOL, hcurr])
      huse
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hlenBound : (decodeLength conf x).toNat * (2 ^ width + 1) ≤
        2 ^ width * (2 ^ width + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _))
    have hbudget : ck + ck' + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, u0, u1, hbudget, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGenGcMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_list conf _ { s with clock := s.clock + (ck + ck' + 1) } ha x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
    · congr 1
    · simp only [s6, s5, setVar, Prod.mk.injEq, true_and]
      rw [temps_updateListEq_twice]
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


/-- Partial generational data traversal has a fuel-based clock bound. -/
theorem genGcPartialMoveDataBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (old gs rs : BitVec width) :
    ∀ (k : Nat) (ha i pa i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveData conf k (ha, i, pa, old, s.memory, s.mdomain, gs, rs) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) →
      s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r0 r1 r2 r5 r6 r7, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7
    h8
  rw [wordGenGcPartialMoveData] at hm
  by_cases hp : ha = pa
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, Nat.zero_le _, ?_⟩
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
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
  have hpb : (!(pa == ha)) = true := by simpa using Ne.symm hp
  by_cases hb : (wordSemTheWord (s.memory ha)).getLsbD 2 = true
  · simp only [hb, if_true] at hm
    generalize hrec : wordGenGcPartialMoveData conf (k - 1) (ha + (decodeLength conf
      (wordSemTheWord (s.memory ha)) + 1) * wordSemBytesInWord, i, pa, old, s.memory,
      s.mdomain, gs, rs) = R at hm
    obtain ⟨i3, pa3, m3, c3⟩ := R
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hrec hb
    simp only [wordSemTheWord] at hrec hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + (decodeLength conf x + 1) * wordSemBytesInWord))
        (setVar 7 (.word ((decodeLength conf x + 1) * wordSemBytesInWord)) s)
    obtain ⟨ck, r0, r1, r2, r5, r6, r7, hprev, hr⟩ := ih (k - 1) (by omega) _ i pa i3 pa3
      m3 s5 hrec hcurr huse hgs hrs
      (by simpa [s5, setVar, FUPDATE_HOL] using h0) (by simpa [s5, setVar, FUPDATE_HOL] using h1)
      (by simpa [s5, setVar, FUPDATE_HOL] using h2) (by simp [s5, setVar, FUPDATE_HOL, h3])
      (by simp [s5, setVar, FUPDATE_HOL, h4]) (by simpa [s5, setVar, FUPDATE_HOL] using h5)
      (by simpa [s5, setVar, FUPDATE_HOL] using h6) (by simp [s5, setVar, FUPDATE_HOL])
      (by simp [s5, setVar, FUPDATE_HOL])
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hbudget : ck + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ck + 1, r0, r1, r2, r5, r6, r7, hbudget, ?_⟩
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_skip conf _ { s with clock := s.clock + (ck + 1) } ha x hws hw2 hlen hshift
      h8 hdm hx hb]
    have hck : s.clock + (ck + 1) ≠ 0 := by omega
    simp only [fixClock, setVar, contLoop, Nat.min_self, if_true, hck, if_false, decClock,
      ← wordGenGcPartialMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcPartialMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
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
    generalize hl : wordGenGcPartialMoveList conf (ha + wordSemBytesInWord,
      decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, old, s.memory,
      s.mdomain, gs, rs) = R at hm
    obtain ⟨ha3, i1, pa1, m1, c1⟩ := R
    simp only at hm
    generalize hrec : wordGenGcPartialMoveData conf (k - 1) (ha3, i1, pa1, old, m1,
      s.mdomain, gs, rs) = R2 at hm
    obtain ⟨i3, pa3, m3, c3⟩ := R2
    simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
    obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
    rw [hx] at hb hl
    simp only [wordSemTheWord] at hb hl
    have hb' : x.getLsbD 2 = false := by simpa using hb
    let s5 : StackSemStateFiniteExact width C F :=
      setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
    obtain ⟨ck, q0, q1, q2, q5, q6, hinner, hL⟩ := genGcPartialMoveListWordBoundedClock
      (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
      conf ha3 gs rs
      ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs,
        by simpa [s5, setVar, FUPDATE_HOL] using h0, by simpa [s5, setVar, FUPDATE_HOL] using h1,
        by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
        by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
      (by simpa [s5, setVar, FUPDATE_HOL] using h6)
      ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
    let s6 : StackSemStateFiniteExact width C F :=
      { s5 with
        memory := m1
        regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
          (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, hprev, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1
      i3 pa3 m3 s6 hrec
      (by simp [s6, s5, setVar, hcurr])
      huse hgs hrs
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
      calc
        _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
    have hlenBound : (decodeLength conf x).toNat * (2 ^ width + 1) ≤
        2 ^ width * (2 ^ width + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _))
    have hbudget : ck + ck' + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, hbudget, ?_⟩
    have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
    have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
        { s with clock := s.clock + (ck + ck' + 1) }) =
        { { s5 with clock := s5.clock + ck } with
          clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
      simp only [s5, setVar]
      congr 1
      omega
    rw [wordGenGcPartialMoveDataCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h3, StackSemStateOps.getVarImm, h8,
      wordSemWordCmp, wordCmpHOL, hpb]
    rw [dataBody_list conf _ { s with clock := s.clock + (ck + ck' + 1) } ha x hw2 hlen
      h8 hdm hx hb', hs5, hadd]
    have hs5c : s5.clock = s.clock := rfl
    have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
      omega
    have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcPartialMoveDataCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcPartialMoveDataCode conf, st)) ?_).trans (hr.trans ?_)
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


/-- Full generational reference traversal has a fuel-based clock bound. -/
theorem genGcMoveRefsBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (ha i pa ib pb ha2 i2 pa2 ib2 pb2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRefs conf k (ha, re, i, pa, ib, pb, old, s.memory, s.mdomain) =
        (ha2, i2, pa2, ib2, pb2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.store.lookup (.temp 4) = some (.word re) →
      s.regs.lookup 0 = some (.word re) → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word ha) →
      ∃ ck r1 r2 r5 r6 r7 t0 t1, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcMoveRefsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb2),
              (.temp 3, .word ib2)]
            regs := s.regs.updateListEq [(0, .word re), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word ha2)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ha i pa ib pb ha2 i2 pa2 ib2 pb2 m2 s hm hcurr huse ht0 ht1 ht2 ht3 ht4 h0 h1 h2 h3 h4
    h5 h6 h7 h8
  rw [wordGenGcMoveRefs] at hm
  by_cases hp : ha = re
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
    obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r1, r2, r5, r6, r7, t0, t1, Nat.zero_le _, ?_⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    rw [wordGenGcMoveRefsCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h0]
    simp [StackSemStateOps.getVarImm, getVar, wordSemWordCmp, wordCmpHOL, fixClock, contLoop,
      StackSemControl.exitLoop, h8]
    apply regs_ext
    intro k
    simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl, FUPDATE_HOL]
    by_cases k0 : k = 0
    · subst k0; simp [h0]
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
  have hpb : (!(re == ha)) = true := by simpa using Ne.symm hp
  generalize hl : wordGenGcMoveList conf (ha + wordSemBytesInWord,
    decodeLength conf (wordSemTheWord (s.memory ha)), i, pa, ib, pb, old, s.memory,
    s.mdomain) = R at hm
  obtain ⟨ha3, i1, pa1, ib1, pb1, m1, c1⟩ := R
  simp only at hm
  generalize hrec : wordGenGcMoveRefs conf (k - 1) (ha3, re, i1, pa1, ib1, pb1, old, m1,
    s.mdomain) = R2 at hm
  obtain ⟨ha4, i3, pa3, ib3, pb3, m3, c3⟩ := R2
  simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨hdm, hisw⟩, rfl, rfl⟩ := hm
  obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
  rw [hx] at hl
  simp only [wordSemTheWord] at hl
  let s5 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
  obtain ⟨ck, q0, q1, q2, q5, q6, g0, g1, hinner, hL⟩ := genGcMoveListWordBoundedClock
    (decodeLength conf x) (ha + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain
    conf ha3 ib ib1 pb pb1
    ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, ht0, ht1, ht2, ht3,
      by simp [s5, setVar, FUPDATE_HOL, h0], by simpa [s5, setVar, FUPDATE_HOL] using h1,
      by simpa [s5, setVar, FUPDATE_HOL] using h2, by simp [s5, getVar, setVar, FUPDATE_HOL, h3],
      by simp [s5, getVar, setVar, FUPDATE_HOL, h4], by simpa [s5, setVar, FUPDATE_HOL] using h5⟩
    (by simpa [s5, setVar, FUPDATE_HOL] using h6)
    ⟨by simp [s5, getVar, setVar, FUPDATE_HOL], by simp [s5, getVar, setVar, FUPDATE_HOL]⟩
  let s6 : StackSemStateFiniteExact width C F :=
    { s5 with
      memory := m1
      store := s5.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb1),
        (.temp 3, .word ib1)]
      regs := s5.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa1),
        (4, .word i1), (5, q5), (6, q6), (7, .word 0), (8, .word ha3)] }
  let s7 : StackSemStateFiniteExact width C F := setVar 0 (.word re) s6
  have hLG : evaluate (.seq (wordGenGcMoveListCode conf) (.get 0 (.temp 4)),
      { s5 with clock := s5.clock + ck }) = (none, s7) := by
    rw [evaluate_seq_none _ _ _ _ hL (by change s5.clock ≤ s5.clock + ck; omega)]
    exact refsRestore_eval s6 re huse (refsTemps_preserve_bound s5.store g0 g1 pb1 ib1 re ht4)
  obtain ⟨ck', r1, r2, r5, r6, r7, u0, u1, hprev, hr⟩ := ih (k - 1) (by omega) ha3 i1 pa1 ib1 pb1
    ha4 i3 pa3 ib3 pb3 m3 s7 hrec
    (by simp [s7, s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, hcurr])
    huse
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (refsTemps_preserve_bound s5.store g0 g1 pb1 ib1 re ht4)
    (by simp [s7, setVar, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s7, s6, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
  have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
    calc
      _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hlenBound : (decodeLength conf x).toNat * (2 ^ width + 1) ≤
      2 ^ width * (2 ^ width + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _))
  have hbudget : ck + ck' + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
  refine ⟨ck + ck' + 1, r1, r2, r5, r6, r7, u0, u1, hbudget, ?_⟩
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hLG, by simp⟩
  have hs5 : setVar 8 (.word (ha + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
      { s with clock := s.clock + (ck + ck' + 1) }) =
      { { s5 with clock := s5.clock + ck } with
        clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
    simp only [s5, setVar]
    congr 1
    omega
  rw [wordGenGcMoveRefsCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, h8,
    wordSemWordCmp, wordCmpHOL, hpb]
  rw [refsBody_eval conf { s with clock := s.clock + (ck + ck' + 1) } ha x hlen
    h8 hdm hx, hs5, hadd]
  have hs7c : s7.clock = s.clock := rfl
  have hmin : min (s.clock + (ck + ck' + 1)) (s7.clock + (ck' + 1)) = s7.clock + (ck' + 1) := by
    omega
  have hck : s7.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcMoveRefsCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcMoveRefsCode conf, st)) ?_).trans (hr.trans ?_)
  · congr 1
  · simp only [s7, s6, s5, setVar, Prod.mk.injEq, true_and]
    rw [temps_updateListEq_twice]
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


/-- Partial generational reference traversal has a fuel-based clock bound. -/
theorem genGcPartialMoveRefListBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (re old : BitVec width) :
    ∀ (k : Nat) (pb i pa : BitVec width) (c : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRefList k conf (pb, i, pa, old, s.memory, s.mdomain, c, gs, rs, re) =
        (i2, pa2, m2, true) →
      s.store.lookup .currHeap = some (.word old) → s.useStore = true →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true → s.regs.lookup 8 = some (.word pb) →
      s.regs.lookup 9 = some (.word re) →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveRefListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pb i pa c i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hc := wordGenGcPartialMoveRefList_ok k rs re pb pa old s.memory i gs s.mdomain conf c i2
    pa2 m2 hm
  rw [wordGenGcPartialMoveRefList] at hm
  by_cases hp : pb = re
  · subst hp
    simp only [if_true, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, -⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    refine ⟨0, r0, r1, r2, r5, r6, r7, .word pb, .word pb, Nat.zero_le _, ?_⟩
    rw [wordGenGcPartialMoveRefListCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp only [getVar, HolRegImm.toWordRegImm, Nat.add_zero, h9]
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
    by_cases k9 : k = 9
    · subst k9; simp [h9]
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9]
  have hk : k ≠ 0 := by
    intro hk; subst hk; simp [hp] at hm
  simp only [hp, hk, if_false] at hm
  subst hc
  generalize hl : wordGenGcPartialMoveList conf (pb + wordSemBytesInWord,
    decodeLength conf (wordSemTheWord (s.memory pb)), i, pa, old, s.memory, s.mdomain, gs,
    rs) = R at hm
  obtain ⟨pb3, i1, pa1, m1, c1⟩ := R
  simp only at hm
  have hc0 := wordGenGcPartialMoveRefList_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm
  simp only [Bool.and_eq_true, Bool.true_and] at hc0
  obtain ⟨⟨hdm, hisw⟩, hc1⟩ := hc0
  subst hc1
  obtain ⟨x, hx⟩ := (isWord_thm _).1 hisw
  rw [hx] at hm hl
  simp only [wordSemTheWord] at hm hl
  let s5 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x)) s)
  obtain ⟨ck, q0, q1, q2, q5, q6, hinner, hL⟩ := genGcPartialMoveListWordBoundedClock
    (decodeLength conf x) (pb + wordSemBytesInWord) s5 pa1 pa old m1 s.memory i1 i s.mdomain conf
    pb3 gs rs
    ⟨hl, hsl, hws, hw2, hlen, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs,
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
  obtain ⟨ck', r0, r1, r2, r5, r6, r7, r8, r9, hprev, hr⟩ := ih (k - 1) (by omega) pb3 i1 pa1 _ i2 pa2
    m2 s6 hm hcurr huse hgs hrs
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [s6, s5, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, h9])
  have hsum : (k - 1) * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width + 1) + 1) = k * (2 ^ width * (2 ^ width + 1) + 1) := by
    calc
      _ = (k - 1 + 1) * (2 ^ width * (2 ^ width + 1) + 1) := by simp [Nat.add_mul]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hlenBound : (decodeLength conf x).toNat * (2 ^ width + 1) ≤
      2 ^ width * (2 ^ width + 1) := Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _))
  have hbudget : ck + ck' + 1 ≤ k * (2 ^ width * (2 ^ width + 1) + 1) := by omega
  refine ⟨ck + ck' + 1, r0, r1, r2, r5, r6, r7, r8, r9, hbudget, ?_⟩
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hL, by simp⟩
  have hs5 : setVar 8 (.word (pb + wordSemBytesInWord)) (setVar 7 (.word (decodeLength conf x))
      { s with clock := s.clock + (ck + ck' + 1) }) =
      { { s5 with clock := s5.clock + ck } with
        clock := { s5 with clock := s5.clock + ck }.clock + (ck' + 1) } := by
    simp only [s5, setVar]
    congr 1
    omega
  have hpb : (!(re == pb)) = true := by simpa using Ne.symm hp
  rw [wordGenGcPartialMoveRefListCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h9, StackSemStateOps.getVarImm, h8,
    wordSemWordCmp, wordCmpHOL, hpb]
  rw [refListBody_eval conf _ { s with clock := s.clock + (ck + ck' + 1) } pb x hlen h8 hdm hx,
    hs5, hadd]
  have hs5c : s5.clock = s.clock := rfl
  have hmin : min (s.clock + (ck + ck' + 1)) (s5.clock + (ck' + 1)) = s5.clock + (ck' + 1) := by
    omega
  have hck : s5.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcPartialMoveRefListCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcPartialMoveRefListCode conf, st)) ?_).trans
    (hr.trans ?_)
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
    by_cases k9 : k = 9
    · subst k9; simp
    simp [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9]


end SteppedFlapjack.StackAllocSteps
