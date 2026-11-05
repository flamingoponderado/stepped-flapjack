import SteppedFlapjack.StackAllocSteps.GenMoveBitmapsCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveRootsBitmaps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveRootsBitmaps

/-! Bounded-clock correctness for generational root traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)
set_option maxHeartbeats 2000000

/-- Full generational bitmap-list bound in the root interface. -/
theorem genGcMoveBitmapsWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init : List (WordLocW width)} :
    ∀ (w : BitVec width) (bitmaps : List (BitVec width)) (z : BitVec width)
      (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa ib pb curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (new stack1 : List (WordLocW width))
      (_a1 i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcMoveBitmaps conf (.word w, stack, bitmaps, i, pa, ib, pb, curr, m, dm) =
          some (new, stack1, i1, pa1, ib1, pb1, m1, true) ∧
        bitmaps.length < 2 ^ width - 1 ∧ goodDimindex width ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.bitmaps = bitmaps ∧ s.useStack = true ∧
        getVar 0 s = some (.word z) ∧ z ≠ 0 ∧
        (s.regs.lookup 1).isSome = true ∧ (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        getVar 9 s = some (.word (w - 1)) ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r9 t0 t1, ck ≤ bitmaps.length * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcMoveBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            clock := s.clock
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length)),
              (9, r9)] }) := by
  rintro w bitmaps z stack s i pa ib pb curr m dm new stack1 _ i1 pa1 ib1 pb1 m1 old
    ⟨hm, hblen, hg, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, rfl, hus, h0, hz, h1,
      h2, h3, h4, h5, h6, h7, h8, h9, ht0, ht1, ht2, ht3, hst, hsp, hbound⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r9, t0, t1, hck, hr⟩ := genGcMoveBitmapsBoundedClock hsl hws hw2 hlen hg hshift init _ w stack old new stack1 i pa
    ib pb curr i1 pa1 ib1 pb1 z m1 s rfl hm hblen hcurr huse hus (by simpa [getVar] using h0) hz
    h1 h2 (by simpa [getVar] using h3) (by simpa [getVar] using h4) h5 h6 h7
    (by simpa [getVar] using h8) (by simpa [getVar] using h9) ht0 ht1 ht2 ht3 hst hsp hbound

  exact ⟨ck, r0, r1, r2, r5, r6, r7, r9, t0, t1, hck.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)), hr⟩


/-- Partial generational bitmap-list bound in the root interface. -/
theorem genGcPartialMoveBitmapsWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init : List (WordLocW width)} {gs rs : BitVec width} :
    ∀ (w : BitVec width) (bitmaps : List (BitVec width)) (z : BitVec width)
      (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa _ib _pb curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (new stack1 : List (WordLocW width))
      (_a1 i1 pa1 _ib1 _pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcPartialMoveBitmaps conf (.word w, stack, bitmaps, i, pa, curr, m, dm, gs, rs) =
          some (new, stack1, i1, pa1, m1, true) ∧
        bitmaps.length < 2 ^ width - 1 ∧ goodDimindex width ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.bitmaps = bitmaps ∧ s.useStack = true ∧
        getVar 0 s = some (.word z) ∧ z ≠ 0 ∧
        (s.regs.lookup 1).isSome = true ∧ (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        getVar 9 s = some (.word (w - 1)) ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r9, ∃ _t0 _t1 : WordLocW width,
        ck ≤ bitmaps.length * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            clock := s.clock
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length)),
              (9, r9)] }) := by
  rintro w bitmaps z stack s i pa _ _ curr m dm new stack1 _ i1 pa1 _ _ m1 old
    ⟨hm, hblen, hg, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, rfl, hus, h0, hz, h1,
      h2, h3, h4, h5, h6, h7, h8, h9, hgs, hrs, hst, hsp, hbound⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r9, hck, h⟩ := genGcPartialMoveBitmapsBoundedClock hsl hws hw2
    hlen hg hshift init _ w stack old new stack1 i pa curr i1 pa1 z m1 s rfl hm hblen hcurr huse
    hus (by simpa [getVar] using h0) hz h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
    (by simpa [getVar] using h9) hgs hrs hst hsp hbound
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r9, .word 0, .word 0, hck.trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)), h⟩


/-- Full generational root traversal has a per-entry clock bound. -/
theorem genGcMoveRootsBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (stack : List (WordLocW width)), stack.length = n →
    ∀ (old stack1 : List (WordLocW width)) (i pa ib pb curr i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveRootsBitmaps conf (stack, s.bitmaps, i, pa, ib, pb, curr, s.memory, s.mdomain) =
        (stack1, i1, pa1, ib1, pb1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (holHd stack) →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9 t0 t1, ck ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
        evaluate (wordGenGcMoveRootsBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ stack1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) ∧
          r9 = .word 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro stack hn old stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 s hm hblen hcurr huse hus h0 h1 h2
    h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  obtain ⟨t0, hrt0⟩ := Option.isSome_iff_exists.1 ht0
  obtain ⟨t1, hrt1⟩ := Option.isSome_iff_exists.1 ht1
  have hm0 := hm
  rw [wordGenGcMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hm] at hm
  rcases stack with _ | ⟨hd, ws⟩
  · simp at hm
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  by_cases h0w : hd = .word 0
  · subst h0w
    simp only [if_true, Prod.mk.injEq, decide_eq_true_eq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    have h00 : (AndOp.and (0#width) (0#width) != (0#width)) = false := by
      change (0#width &&& 0#width != 0#width) = false
      simp
    refine ⟨0, r0, r1, r2, r5, r6, r7, .word (wordSemBytesInWord * BitVec.ofNat width old.length),
      .word 0, t0, t1, Nat.zero_le _, ?_, rfl⟩
    rw [genGcMove_skip_store s t0 t1 _ _ hrt0 hrt1 ht2 ht3]
    simp only [holHd] at h9
    rw [wordGenGcMoveRootsBitmapsCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
      fixClock, contLoop, StackSemControl.exitLoop, h9, h00]
    refine ⟨?_, by simp [hst]⟩
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
  simp only [h0w, if_false] at hm
  generalize hbm : wordGenGcMoveBitmaps conf (hd, ws, s.bitmaps, i, pa, ib, pb, curr, s.memory,
    s.mdomain) = R at hm
  rcases R with _ | ⟨new, st, i2, pa2, ib2, pb2, m2, c2⟩
  · simp at hm
  simp only at hm
  generalize hrec : wordGenGcMoveRootsBitmaps conf (st, s.bitmaps, i2, pa2, ib2, pb2, curr, m2,
    s.mdomain) = R2 at hm
  obtain ⟨st', i', pa', ib', pb', m', c3⟩ := R2
  simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hc2, hc3⟩ := hm
  subst hc2 hc3
  obtain ⟨c, rfl⟩ : ∃ c, hd = .word c := by
    cases hd with
    | word c => exact ⟨c, rfl⟩
    | loc l1 l2 => simp [wordGenGcMoveBitmaps, StackSem.fullReadBitmap] at hbm
  have hc0 : c ≠ 0 := fun h => h0w (by rw [h])
  rcases st with _ | ⟨h, tl⟩
  · have := wordGenGcMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hrec
    rw [this] at hrec
    simp at hrec
  have hlenB := wordGenGcMoveBitmaps_LENGTH hbm
  simp only [holHd] at h9
  have hB8 : wordSemBytesInWord * BitVec.ofNat width old.length + wordSemBytesInWord =
      wordSemBytesInWord * BitVec.ofNat width (old ++ [WordLocW.word c]).length := by
    simp [List.length_append, BitVec.ofNat_add, BitVec.mul_add]
  -- the state entering `word_gen_gc_move_bitmaps_code`
  let s2 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [WordLocW.word c]).length))
      (setVar 9 (.word (c - 1)) (setVar 0 (.word c) s))
  obtain ⟨ckB, q0, q1, q2, q5, q6, q7, q9, g0, g1, hBbound, hBm⟩ :=
    genGcMoveBitmapsWordBoundedClock (init := init)
      c s.bitmaps c ws s2 i pa ib pb curr s.memory s.mdomain new (h :: tl) pa i2 pa2 ib2 pb2 m2
      (old ++ [WordLocW.word c])
      ⟨hbm, hblen, hg, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, rfl, hus,
        by simp [s2, getVar, setVar, FUPDATE_HOL], hc0,
        by simpa [s2, setVar, FUPDATE_HOL] using h1, by simpa [s2, setVar, FUPDATE_HOL] using h2,
        by simp [s2, getVar, setVar, FUPDATE_HOL, h3], by simp [s2, getVar, setVar, FUPDATE_HOL, h4],
        by simpa [s2, setVar, FUPDATE_HOL] using h5, by simpa [s2, setVar, FUPDATE_HOL] using h6,
        by simpa [s2, setVar, FUPDATE_HOL] using h7, by simp [s2, getVar, setVar, FUPDATE_HOL],
        by simp [s2, getVar, setVar, FUPDATE_HOL], ht0, ht1, ht2, ht3,
        by simp [s2, setVar, hst], hsp, by simpa [s2, setVar] using hbound⟩
  let s3 : StackSemStateFiniteExact width C F :=
    { s2 with
      memory := m2
      stack := init ++ (old ++ [WordLocW.word c]) ++ new ++ h :: tl
      clock := s2.clock
      store := s2.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb2),
        (.temp 3, .word ib2)]
      regs := s2.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa2), (4, .word i2),
        (5, q5), (6, q6), (7, q7),
        (8, .word (wordSemBytesInWord *
          BitVec.ofNat width (old ++ [WordLocW.word c] ++ new).length)),
        (9, q9)] }
  have hslen : s3.stack.length = s.stack.length := by
    simp only [s3, hst, List.length_append, List.length_cons, List.length_nil] at hlenB ⊢
    omega
  have hJ : (width / 8) * (old ++ [WordLocW.word c] ++ new).length < 2 ^ width := by
    refine Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) hbound
    simp only [hst, List.length_append, List.length_cons, List.length_nil] at hlenB ⊢
    omega
  have hjJ : s3.stackSpace + (old ++ [WordLocW.word c] ++ new).length < s3.stack.length := by
    simp only [s3, s2, setVar, hsp, List.length_append, List.length_cons, List.length_nil]
    omega
  have hvJ : s3.stack[s3.stackSpace + (old ++ [WordLocW.word c] ++ new).length]'hjJ = h := by
    simp only [s3, s2, setVar, hsp]
    simp
  -- the state the next frame starts from
  let t : StackSemStateFiniteExact width C F := setVar 9 h s3
  have hlen8 : (old ++ [WordLocW.word c] ++ new).length = (old ++ WordLocW.word c :: new).length := by
    simp
  obtain ⟨ck', r0, r1, r2, r5, r6, r7, r8, r9, u0, u1, hprev, hr, hr9⟩ := ih (h :: tl).length
    (by simp only [List.length_cons] at hlenB hn ⊢; omega) (h :: tl) rfl
    (old ++ WordLocW.word c :: new) st' i2 pa2 ib2 pb2 curr i' pa' ib' pb' m' t hrec hblen
    (by simp [t, s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      FUPDATE_HOL, hcurr])
    huse hus
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by
      rw [← hlen8]
      simp only [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl]
      simp)
    (by simp [t, setVar, FUPDATE_HOL, holHd])
    (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simp [t, s3, setVar]) (by simpa [t, s3, s2, setVar] using hsp)
    (by
      have : t.stack.length = s.stack.length := hslen
      rw [this]
      exact hbound)
  have hbmBound : s.bitmaps.length * (2 ^ width * (2 ^ width + 1) + 1) ≤
      2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hsum : (h :: tl).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by
    have hh := Nat.mul_le_mul_right (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) (show (h :: tl).length + 1 ≤ n by
      simp only [List.length_cons] at hlenB hn ⊢; omega)
    simpa [Nat.add_mul] using hh
  have hbudget : ckB + ck' + 1 ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by omega
  refine ⟨ckB + ck' + 1, r0, r1, r2, r5, r6, r7, r8, r9, u0, u1, hbudget, ?_, hr9⟩
  have hcc : (AndOp.and c c != (0 : BitVec width)) = true := by
    have : ¬ AndOp.and c c = (0 : BitVec width) := by
      change ¬ c &&& c = 0
      simpa using hc0
    simpa [bne] using this
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hBm, by simp⟩
  have hs2 : setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width old.length +
      wordSemBytesInWord)) (setVar 9 (.word (c - 1)) (setVar 0 (.word c)
        { s with clock := s.clock + (ckB + ck' + 1) })) =
      { { s2 with clock := s2.clock + ckB } with
        clock := { s2 with clock := s2.clock + ckB }.clock + (ck' + 1) } := by
    simp only [s2, setVar, hB8]
    congr 1
    omega
  rw [wordGenGcMoveRootsBitmapsCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h9, StackSemStateOps.getVarImm, wordSemWordCmp,
    wordCmpHOL, hcc]
  rw [evaluate_seq_none _ _ _ _
      (moveHOL_eval { s with clock := s.clock + (ckB + ck' + 1) } 0 9 c h9) le_rfl,
    evaluate_seq_none _ _ _ _
      (sub1Inst_eval (setVar 0 (.word c) { s with clock := s.clock + (ckB + ck' + 1) }) 9 c
        (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h9])) le_rfl,
    evaluate_seq_none _ _ _ _
      (addBytesInWordInst_eval (setVar 9 (.word (c - 1))
        (setVar 0 (.word c) { s with clock := s.clock + (ckB + ck' + 1) })) 8
        (wordSemBytesInWord * BitVec.ofNat width old.length)
        (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h8])) le_rfl,
    hs2, evaluate_seq_none _ _ _ _ hadd (by simp [s2, setVar]),
    stackLoadAny_eval { s3 with clock := s3.clock + (ck' + 1) } 9 8 _ hus
      (by simp [s3, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      hg hJ hjJ, hvJ]
  have hs3c : s3.clock = s.clock := rfl
  have hmin : min (s.clock + (ckB + ck' + 1)) (s3.clock + (ck' + 1)) = s3.clock + (ck' + 1) := by
    omega
  have hck : s3.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, setVar, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcMoveRootsBitmapsCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcMoveRootsBitmapsCode conf, st)) ?_).trans
    (hr.trans ?_)
  · simp only [t, setVar]
    congr 1
  · simp only [t, s3, s2, setVar, Prod.mk.injEq, true_and]
    rw [temps_updateListEq_twice]
    congr 1
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
    · simp


/-- Partial generational root traversal has a per-entry clock bound. -/
theorem genGcPartialMoveRootsBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (n : Nat) (stack : List (WordLocW width)), stack.length = n →
    ∀ (old stack1 : List (WordLocW width)) (i pa curr i1 pa1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRootsBitmaps conf (stack, s.bitmaps, i, pa, curr, s.memory, s.mdomain,
        gs, rs) = (stack1, i1, pa1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      (s.regs.lookup 0).isSome = true → (s.regs.lookup 1).isSome = true →
      (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (holHd stack) →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9, ck ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveRootsBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ stack1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) ∧
          r9 = .word 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro stack hn old stack1 i pa curr i1 pa1 m1 s hm hblen hcurr huse hus h0 h1 h2
    h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  have hm0 := hm
  rw [wordGenGcPartialMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hm] at hm
  rcases stack with _ | ⟨hd, ws⟩
  · simp at hm
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  by_cases h0w : hd = .word 0
  · subst h0w
    simp only [if_true, Prod.mk.injEq, decide_eq_true_eq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hm
    obtain ⟨r0, hr0⟩ := Option.isSome_iff_exists.1 h0
    obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨r2, hr2⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨r5, hr5⟩ := Option.isSome_iff_exists.1 h5
    obtain ⟨r6, hr6⟩ := Option.isSome_iff_exists.1 h6
    obtain ⟨r7, hr7⟩ := Option.isSome_iff_exists.1 h7
    have h00 : (AndOp.and (0#width) (0#width) != (0#width)) = false := by
      change (0#width &&& 0#width != 0#width) = false
      simp
    refine ⟨0, r0, r1, r2, r5, r6, r7, .word (wordSemBytesInWord * BitVec.ofNat width old.length),
      .word 0, Nat.zero_le _, ?_, rfl⟩
    simp only [holHd] at h9
    rw [wordGenGcPartialMoveRootsBitmapsCode_eq, evaluate_loop, evaluate_ite, evaluate_break]
    simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
      fixClock, contLoop, StackSemControl.exitLoop, h9, h00]
    refine ⟨?_, by simp [hst]⟩
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
  simp only [h0w, if_false] at hm
  generalize hbm : wordGenGcPartialMoveBitmaps conf (hd, ws, s.bitmaps, i, pa, curr, s.memory,
    s.mdomain, gs, rs) = R at hm
  rcases R with _ | ⟨new, st, i2, pa2, m2, c2⟩
  · simp at hm
  simp only at hm
  generalize hrec : wordGenGcPartialMoveRootsBitmaps conf (st, s.bitmaps, i2, pa2, curr, m2,
    s.mdomain, gs, rs) = R2 at hm
  obtain ⟨st', i', pa', m', c3⟩ := R2
  simp only [Prod.mk.injEq, Bool.and_eq_true] at hm
  obtain ⟨rfl, rfl, rfl, rfl, hc2, hc3⟩ := hm
  subst hc2 hc3
  obtain ⟨c, rfl⟩ : ∃ c, hd = .word c := by
    cases hd with
    | word c => exact ⟨c, rfl⟩
    | loc l1 l2 => simp [wordGenGcPartialMoveBitmaps, StackSem.fullReadBitmap] at hbm
  have hc0 : c ≠ 0 := fun h => h0w (by rw [h])
  rcases st with _ | ⟨h, tl⟩
  · have := wordGenGcPartialMoveRootsBitmaps_unroll _ _ _ _ _ _ _ _ hrec
    rw [this] at hrec
    simp at hrec
  have hlenB := wordGenGcPartialMoveBitmaps_LENGTH hbm
  simp only [holHd] at h9
  have hB8 : wordSemBytesInWord * BitVec.ofNat width old.length + wordSemBytesInWord =
      wordSemBytesInWord * BitVec.ofNat width (old ++ [WordLocW.word c]).length := by
    simp [List.length_append, BitVec.ofNat_add, BitVec.mul_add]
  -- the state entering `word_gen_gc_partial_move_bitmaps_code`
  let s2 : StackSemStateFiniteExact width C F :=
    setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width (old ++ [WordLocW.word c]).length))
      (setVar 9 (.word (c - 1)) (setVar 0 (.word c) s))
  obtain ⟨ckB, q0, q1, q2, q5, q6, q7, q9, -, -, hBbound, hBm⟩ :=
    genGcPartialMoveBitmapsWordBoundedClock (init := init) (gs := gs) (rs := rs)
      c s.bitmaps c ws s2 i pa pa pa curr s.memory s.mdomain new (h :: tl) pa i2 pa2 pa pa m2
      (old ++ [WordLocW.word c])
      ⟨hbm, hblen, hg, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, rfl, hus,
        by simp [s2, getVar, setVar, FUPDATE_HOL], hc0,
        by simpa [s2, setVar, FUPDATE_HOL] using h1, by simpa [s2, setVar, FUPDATE_HOL] using h2,
        by simp [s2, getVar, setVar, FUPDATE_HOL, h3], by simp [s2, getVar, setVar, FUPDATE_HOL, h4],
        by simpa [s2, setVar, FUPDATE_HOL] using h5, by simpa [s2, setVar, FUPDATE_HOL] using h6,
        by simpa [s2, setVar, FUPDATE_HOL] using h7, by simp [s2, getVar, setVar, FUPDATE_HOL],
        by simp [s2, getVar, setVar, FUPDATE_HOL], hgs, hrs,
        by simp [s2, setVar, hst], hsp, by simpa [s2, setVar] using hbound⟩
  let s3 : StackSemStateFiniteExact width C F :=
    { s2 with
      memory := m2
      stack := init ++ (old ++ [WordLocW.word c]) ++ new ++ h :: tl
      clock := s2.clock
      regs := s2.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa2), (4, .word i2),
        (5, q5), (6, q6), (7, q7),
        (8, .word (wordSemBytesInWord *
          BitVec.ofNat width (old ++ [WordLocW.word c] ++ new).length)),
        (9, q9)] }
  have hslen : s3.stack.length = s.stack.length := by
    simp only [s3, hst, List.length_append, List.length_cons, List.length_nil] at hlenB ⊢
    omega
  have hJ : (width / 8) * (old ++ [WordLocW.word c] ++ new).length < 2 ^ width := by
    refine Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) hbound
    simp only [hst, List.length_append, List.length_cons, List.length_nil] at hlenB ⊢
    omega
  have hjJ : s3.stackSpace + (old ++ [WordLocW.word c] ++ new).length < s3.stack.length := by
    simp only [s3, s2, setVar, hsp, List.length_append, List.length_cons, List.length_nil]
    omega
  have hvJ : s3.stack[s3.stackSpace + (old ++ [WordLocW.word c] ++ new).length]'hjJ = h := by
    simp only [s3, s2, setVar, hsp]
    simp
  -- the state the next frame starts from
  let t : StackSemStateFiniteExact width C F := setVar 9 h s3
  have hlen8 : (old ++ [WordLocW.word c] ++ new).length = (old ++ WordLocW.word c :: new).length := by
    simp
  obtain ⟨ck', r0, r1, r2, r5, r6, r7, r8, r9, hprev, hr, hr9⟩ := ih (h :: tl).length
    (by simp only [List.length_cons] at hlenB hn ⊢; omega) (h :: tl) rfl
    (old ++ WordLocW.word c :: new) st' i2 pa2 curr i' pa' m' t hrec hblen
    (by simp [t, s3, s2, setVar, hcurr])
    huse hus
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
    (by
      rw [← hlen8]
      simp only [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq,
        HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl]
      simp)
    (by simp [t, setVar, FUPDATE_HOL, holHd])
    (by simpa [t, s3, s2, setVar] using hgs) (by simpa [t, s3, s2, setVar] using hrs)
    (by simp [t, s3, setVar]) (by simpa [t, s3, s2, setVar] using hsp)
    (by
      have : t.stack.length = s.stack.length := hslen
      rw [this]
      exact hbound)
  have hbmBound : s.bitmaps.length * (2 ^ width * (2 ^ width + 1) + 1) ≤
      2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hsum : (h :: tl).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by
    have hh := Nat.mul_le_mul_right (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) (show (h :: tl).length + 1 ≤ n by
      simp only [List.length_cons] at hlenB hn ⊢; omega)
    simpa [Nat.add_mul] using hh
  have hbudget : ckB + ck' + 1 ≤ n * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by omega
  refine ⟨ckB + ck' + 1, r0, r1, r2, r5, r6, r7, r8, r9, hbudget, ?_, hr9⟩
  have hcc : (AndOp.and c c != (0 : BitVec width)) = true := by
    have : ¬ AndOp.and c c = (0 : BitVec width) := by
      change ¬ c &&& c = 0
      simpa using hc0
    simpa [bne] using this
  have hadd := StackProps.evaluateAddClock (ck' + 1) _ _ _ _ ⟨hBm, by simp⟩
  have hs2 : setVar 8 (.word (wordSemBytesInWord * BitVec.ofNat width old.length +
      wordSemBytesInWord)) (setVar 9 (.word (c - 1)) (setVar 0 (.word c)
        { s with clock := s.clock + (ckB + ck' + 1) })) =
      { { s2 with clock := s2.clock + ckB } with
        clock := { s2 with clock := s2.clock + ckB }.clock + (ck' + 1) } := by
    simp only [s2, setVar, hB8]
    congr 1
    omega
  rw [wordGenGcPartialMoveRootsBitmapsCode_eq, evaluate_loop, evaluate_ite]
  simp only [getVar, HolRegImm.toWordRegImm, h9, StackSemStateOps.getVarImm, wordSemWordCmp,
    wordCmpHOL, hcc]
  rw [evaluate_seq_none _ _ _ _
      (moveHOL_eval { s with clock := s.clock + (ckB + ck' + 1) } 0 9 c h9) le_rfl,
    evaluate_seq_none _ _ _ _
      (sub1Inst_eval (setVar 0 (.word c) { s with clock := s.clock + (ckB + ck' + 1) }) 9 c
        (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h9])) le_rfl,
    evaluate_seq_none _ _ _ _
      (addBytesInWordInst_eval (setVar 9 (.word (c - 1))
        (setVar 0 (.word c) { s with clock := s.clock + (ckB + ck' + 1) })) 8
        (wordSemBytesInWord * BitVec.ofNat width old.length)
        (by simp [setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq, h8])) le_rfl,
    hs2, evaluate_seq_none _ _ _ _ hadd (by simp [s2, setVar]),
    stackLoadAny_eval { s3 with clock := s3.clock + (ck' + 1) } 9 8 _ hus
      (by simp [s3, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      hg hJ hjJ, hvJ]
  have hs3c : s3.clock = s.clock := rfl
  have hmin : min (s.clock + (ckB + ck' + 1)) (s3.clock + (ck' + 1)) = s3.clock + (ck' + 1) := by
    omega
  have hck : s3.clock + (ck' + 1) ≠ 0 := by omega
  simp only [fixClock, setVar, contLoop, hmin, if_true, hck, if_false, decClock,
    ← wordGenGcPartialMoveRootsBitmapsCode_eq]
  refine (congrArg (fun st => evaluate (wordGenGcPartialMoveRootsBitmapsCode conf, st)) ?_).trans
    (hr.trans ?_)
  · simp only [t, setVar]
    congr 1
  · simp only [t, s3, s2, setVar, Prod.mk.injEq, true_and]
    congr 1
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
    · simp


end SteppedFlapjack.StackAllocSteps
