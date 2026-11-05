import SteppedFlapjack.StackAllocSteps.GenMoveBitmapCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveBitmaps
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenPartialMoveBitmaps

/-! Bounded-clock correctness for generational bitmap-list traversal. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackRemove (loadInst storeInst leftShiftInst rightShiftInst)
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
set_option maxHeartbeats 2000000

/-- Full generational bitmap bound in the bitmap-list interface. -/
theorem genGcMoveBitmapWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init : List (WordLocW width)} :
    ∀ (w : BitVec width) (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa ib pb curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (new stack1 : List (WordLocW width))
      (_a1 i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcMoveBitmap conf (w, stack, i, pa, ib, pb, curr, m, dm) =
          some (new, stack1, i1, pa1, ib1, pb1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.useStack = true ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        getVar 7 s = some (.word w) ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 t0 t1, ck ≤ w.toNat * (2 ^ width + 1) ∧
        evaluate (wordGenGcMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  rintro w stack s i pa ib pb curr m dm new stack1 _ i1 pa1 ib1 pb1 m1 old
    ⟨hm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus, h0, h1, h2, h3, h4, h5, h6,
      h7, h8, ht0, ht1, ht2, ht3, hst, hsp, hbound⟩
  exact genGcMoveBitmapBoundedClock hsl hws hw2 hlen hg hshift init w.toNat w rfl stack old new
    stack1 i pa ib pb curr i1 pa1 ib1 pb1 m1 s hm hcurr huse hus h0 h1 h2
    (by simpa [getVar] using h3) (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7)
    (by simpa [getVar] using h8) ht0 ht1 ht2 ht3 hst hsp hbound


/-- Partial generational bitmap bound in the bitmap-list interface. -/
theorem genGcPartialMoveBitmapWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init : List (WordLocW width)} {gs rs : BitVec width} :
    ∀ (w : BitVec width) (stack : List (WordLocW width)) (s : StackSemStateFiniteExact width C F)
      (i pa curr : BitVec width) (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (new stack1 : List (WordLocW width)) (_a1 i1 pa1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (old : List (WordLocW width)),
      wordGenGcPartialMoveBitmap conf (w, stack, i, pa, curr, m, dm, gs, rs) =
          some (new, stack1, i1, pa1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.useStack = true ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        getVar 7 s = some (.word w) ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7, ck ≤ w.toNat * (2 ^ width + 1) ∧
        evaluate (wordGenGcPartialMoveBitmapCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length))] }) := by
  rintro w stack s i pa curr m dm new stack1 _ i1 pa1 m1 old
    ⟨hm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus, h0, h1, h2, h3, h4, h5, h6,
      h7, h8, hgs, hrs, hst, hsp, hbound⟩
  exact genGcPartialMoveBitmapBoundedClock hsl hws hw2 hlen hg hshift init w.toNat w rfl stack old
    new stack1 i pa curr i1 pa1 m1 s hm hcurr huse hus h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 (by simpa [getVar] using h7) (by simpa [getVar] using h8)
    hgs hrs hst hsp hbound


/-- Full generational bitmap-list traversal has a word-count clock bound. -/
theorem genGcMoveBitmapsBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (d : Nat) (w : BitVec width) (stack old new stack1 : List (WordLocW width))
      (i pa ib pb curr i1 pa1 ib1 pb1 z : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      s.bitmaps.length - (w - 1).toNat = d →
      wordGenGcMoveBitmaps conf (.word w, stack, s.bitmaps, i, pa, ib, pb, curr, s.memory,
        s.mdomain) = some (new, stack1, i1, pa1, ib1, pb1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      s.regs.lookup 0 = some (.word z) → z ≠ 0 →
      (s.regs.lookup 1).isSome = true → (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (.word (w - 1)) →
      (s.store.lookup (.temp 0)).isSome = true → (s.store.lookup (.temp 1)).isSome = true →
      s.store.lookup (.temp 2) = some (.word pb) → s.store.lookup (.temp 3) = some (.word ib) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r9 t0 t1, ck ≤ d * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcMoveBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length)),
              (9, r9)] }) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro w stack old new stack1 i pa ib pb curr i1 pa1 ib1 pb1 z m1 s hd hm hblen hcurr huse hus h0
    hz h1 h2 h3 h4 h5 h6 h7 h8 h9 ht0 ht1 ht2 ht3 hst hsp hbound
  have hm0 := hm
  rw [wordGenGcMoveBitmaps_unroll ⟨hm, hblen, hg⟩] at hm
  generalize hdr : s.bitmaps.drop (w - 1).toNat = D at hm
  rcases D with _ | ⟨y, ys⟩
  · simp at hm
  have hidx : (w - 1).toNat < s.bitmaps.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hdr
    simp at hdr
  have hy : s.bitmaps[(w - 1).toNat] = y := by
    rw [List.drop_eq_getElem_cons hidx] at hdr
    simp only [List.cons.injEq] at hdr
    exact hdr.1
  simp only at hm
  generalize hbm : wordGenGcMoveBitmap conf (y, stack, i, pa, ib, pb, curr, s.memory,
    s.mdomain) = R at hm
  rcases R with _ | ⟨hd1, ws, i2, pa2, ib2, pb2, m2, c2⟩
  · simp at hm
  simp only at hm
  have hc2 : c2 = true := by
    by_cases hmsb : y.msb = true
    · simp only [hmsb, not_true_eq_false, if_false] at hm
      split at hm
      · simp at hm
      · simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
        exact hm.2.2.2.2.2.2.2.1
    · simp only [hmsb, Bool.false_eq_true, not_false_eq_true, if_true, Option.some.injEq,
        Prod.mk.injEq] at hm
      exact hm.2.2.2.2.2.2.2
  subst hc2
  -- one `word_gen_gc_move_bitmap_code` run on the loaded bitmap word
  let s2 : StackSemStateFiniteExact width C F := setVar 7 (.word y) s
  obtain ⟨ckB, q0, q1, q2, q5, q6, q7, g0, g1, hBbound, hB⟩ := genGcMoveBitmapWordBoundedClock
    (init := init) y stack s2 i pa ib pb curr s.memory s.mdomain hd1 ws pa i2 pa2 ib2 pb2 m2 old
    ⟨hbm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus,
      by simp [s2, setVar, FUPDATE_HOL, h0], by simpa [s2, setVar, FUPDATE_HOL] using h1,
      by simpa [s2, setVar, FUPDATE_HOL] using h2, by simp [s2, getVar, setVar, FUPDATE_HOL, h3],
      by simp [s2, getVar, setVar, FUPDATE_HOL, h4], by simpa [s2, setVar, FUPDATE_HOL] using h5,
      by simpa [s2, setVar, FUPDATE_HOL] using h6, by simp [s2, getVar, setVar, FUPDATE_HOL],
      by simp [s2, getVar, setVar, FUPDATE_HOL, h8], ht0, ht1, ht2, ht3,
      by simp [s2, setVar, hst], hsp, by simpa [s2, setVar] using hbound⟩
  let s3 : StackSemStateFiniteExact width C F :=
    { s2 with
      memory := m2
      stack := init ++ old ++ hd1 ++ ws
      store := s2.store.updateListEq [(.temp 0, g0), (.temp 1, g1), (.temp 2, .word pb2),
        (.temp 3, .word ib2)]
      regs := s2.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa2), (4, .word i2),
        (5, q5), (6, q6), (7, q7),
        (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ hd1).length))] }
  -- the state after one loop body
  let t : StackSemStateFiniteExact width C F :=
    setVar 0 (.word (y >>> (width - 1))) (setVar 9 (.word (w - 1 + 1)) (setVar 0 (.word y) s3))
  have h9c : s3.regs.lookup 9 = some (.word (w - 1)) := by
    simp [s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, h9]
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hm1 : (width - 1) % 2 ^ width = width - 1 := Nat.mod_eq_of_lt (by omega)
  have hl1 : ¬ width ≤ width - 1 := by omega
  have hbody : ∀ e, evaluate (.seq (.bitmapLoad 7 9) (.seq (wordGenGcMoveBitmapCode conf)
      (.seq (.bitmapLoad 0 9) (.seq (add1Inst 9) (rightShiftInst 0 (width - 1))))),
      { s with clock := s.clock + (ckB + e) }) = (none, { t with clock := t.clock + e }) := by
    intro e
    have hadd := StackProps.evaluateAddClock e _ _ _ _ ⟨hB, by simp⟩
    have hs2 : setVar 7 (.word y) { s with clock := s.clock + (ckB + e) } =
        { { s2 with clock := s2.clock + ckB } with
          clock := { s2 with clock := s2.clock + ckB }.clock + e } := by
      simp only [s2, setVar]
      congr 1
      omega
    rw [evaluate_seq_none _ _ _ _ (bitmapLoad_eval { s with clock := s.clock + (ckB + e) } 7 9
        (w - 1) y hus (by decide) h9 hidx hy) le_rfl,
      hs2, evaluate_seq_none _ _ _ _ hadd (by simp [s2, setVar]),
      evaluate_seq_none _ _ _ _ (bitmapLoad_eval { s3 with clock := s3.clock + e } 0 9 (w - 1) y
        hus (by decide) h9c hidx hy) le_rfl]
    simp [evaluate_seq, evaluate_inst, add1Inst, rightShiftInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordShiftHOL, hm1, hl1, t, s3, s2,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, h9]
  have hzz : (AndOp.and z z != (0 : BitVec width)) = true := by
    have : ¬ AndOp.and z z = (0 : BitVec width) := by
      change ¬ z &&& z = 0
      simpa using hz
    simpa [bne] using this
  have htc : t.clock = s.clock := rfl
  have hword : y.toNat * (2 ^ width + 1) ≤ 2 ^ width * (2 ^ width + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt y.isLt)
  have hdpos : 1 ≤ d := by omega
  by_cases hmsb : y.msb = true
  · simp only [hmsb, not_true_eq_false, if_false] at hm
    generalize hrec : wordGenGcMoveBitmaps conf (.word (w + 1), ws, s.bitmaps, i2, pa2, ib2, pb2,
      curr, m2, s.mdomain) = R3 at hm
    rcases R3 with _ | ⟨hd3, st3, i3, pa3, ib3, pb3, m3, c3⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, rfl⟩ := hm
    have hz' : y >>> (width - 1) ≠ 0 := word_msb_IFF_lsr_EQ_0.1 hmsb
    have hlenA := wordGenGcMoveBitmaps_LENGTH hm0
    have hlenB := wordGenGcMoveBitmaps_LENGTH hrec
    have hwn : w.toNat = (w - 1).toNat + 1 := by
      have h := BitVec.toNat_add (w - 1) 1
      rw [BitVec.sub_add_cancel] at h
      rw [h]
      have h1 : (1 : BitVec width).toNat = 1 := by
        simp [Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
      rw [h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hdec : t.bitmaps.length - (w + 1 - 1).toNat < d := by
      simp only [t, s3, s2, setVar, BitVec.add_sub_cancel]
      omega
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, r9, u0, u1, hprev, hr⟩ := ih _ hdec (w + 1) ws (old ++ hd1) hd3
      st3 i2 pa2 ib2 pb2 curr i3 pa3 ib3 pb3 (y >>> (width - 1)) m3 t rfl hrec hblen
      (by simp [t, s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
        FUPDATE_HOL, hcurr])
      huse hus
      (by simp [t, setVar, FUPDATE_HOL]) hz'
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, setVar, FUPDATE_HOL, BitVec.sub_add_cancel, BitVec.add_sub_cancel])
      (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [t, s3, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simp [t, s3, setVar]) hsp
      (by
        have hl : (init ++ old ++ hd1 ++ ws).length = s.stack.length := by
          simp only [hst, List.length_append] at hlenA hlenB ⊢
          omega
        simp only [t, s3, s2, setVar]
        rw [hl]
        exact hbound)
    have hsum : (t.bitmaps.length - (w + 1 - 1).toNat) * (2 ^ width * (2 ^ width + 1) + 1) +
        (2 ^ width * (2 ^ width + 1) + 1) ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by
      have hh := Nat.mul_le_mul_right (2 ^ width * (2 ^ width + 1) + 1) (show t.bitmaps.length - (w + 1 - 1).toNat + 1 ≤ d by omega)
      simpa [Nat.add_mul] using hh
    have hbudget : ckB + ck' + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ckB + ck' + 1, r0, r1, r2, r5, r6, r7, r9, u0, u1, hbudget, ?_⟩
    rw [wordGenGcMoveBitmapsCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hzz]
    rw [show ckB + ck' + 1 = ckB + (ck' + 1) by omega, hbody (ck' + 1)]
    have hmin : min (s.clock + (ckB + (ck' + 1))) (t.clock + (ck' + 1)) = t.clock + (ck' + 1) := by
      omega
    have hck : t.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcMoveBitmapsCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcMoveBitmapsCode conf, st)) ?_).trans
      (hr.trans ?_)
    · congr 1
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
  · simp only [hmsb, Bool.false_eq_true, not_false_eq_true, if_true, Option.some.injEq,
      Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    have hz0 : y >>> (width - 1) = 0 := by
      by_contra hne
      exact hmsb (word_msb_IFF_lsr_EQ_0.2 hne)
    have hsum : 2 ^ width * (2 ^ width + 1) + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by
      simpa using Nat.mul_le_mul_right (2 ^ width * (2 ^ width + 1) + 1) hdpos
    have hbudget : ckB + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ckB + 1, .word (y >>> (width - 1)), q1, q2, q5, q6, q7, .word (w - 1 + 1), g0, g1, hbudget, ?_⟩
    rw [wordGenGcMoveBitmapsCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hzz]
    rw [hbody 1]
    have hmin : min (s.clock + (ckB + 1)) (t.clock + 1) = t.clock + 1 := by omega
    have hck : t.clock + 1 ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock]
    have h00 : (AndOp.and (0#width) (0#width) != (0#width)) = false := by
      change (0#width &&& 0#width != 0#width) = false
      simp
    rw [evaluate_loop, evaluate_ite, evaluate_break]
    simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
      fixClock, contLoop, StackSemControl.exitLoop, t, setVar, FUPDATE_HOL,
      HolFiniteMapExact.lookup_updateEq, hz0, h00]
    refine ⟨?_, by simp [s3, s2, setVar]⟩
    apply regs_ext
    intro k
    simp only [s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
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


/-- Partial generational bitmap-list traversal has a word-count clock bound. -/
theorem genGcPartialMoveBitmapsBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width) (hw2 : 2 < width)
    (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord)
    (init : List (WordLocW width)) :
    ∀ (d : Nat) (w : BitVec width) (stack old new stack1 : List (WordLocW width))
      (i pa curr i1 pa1 z : BitVec width) (m1 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      s.bitmaps.length - (w - 1).toNat = d →
      wordGenGcPartialMoveBitmaps conf (.word w, stack, s.bitmaps, i, pa, curr, s.memory,
        s.mdomain, gs, rs) = some (new, stack1, i1, pa1, m1, true) →
      s.bitmaps.length < 2 ^ width - 1 →
      s.store.lookup .currHeap = some (.word curr) → s.useStore = true → s.useStack = true →
      s.regs.lookup 0 = some (.word z) → z ≠ 0 →
      (s.regs.lookup 1).isSome = true → (s.regs.lookup 2).isSome = true →
      s.regs.lookup 3 = some (.word pa) → s.regs.lookup 4 = some (.word i) →
      (s.regs.lookup 5).isSome = true → (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      s.regs.lookup 8 = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) →
      s.regs.lookup 9 = some (.word (w - 1)) →
      s.store.lookup (.temp 0) = some (.word gs) → s.store.lookup (.temp 1) = some (.word rs) →
      s.stack = init ++ old ++ stack → s.stackSpace = init.length →
      (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r9, ck ≤ d * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ new ++ stack1
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7),
              (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ new).length)),
              (9, r9)] }) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro w stack old new stack1 i pa curr i1 pa1 z m1 s hd hm hblen hcurr huse hus h0
    hz h1 h2 h3 h4 h5 h6 h7 h8 h9 hgs hrs hst hsp hbound
  have hm0 := hm
  rw [wordGenGcPartialMoveBitmaps_unroll ⟨hm, hblen, hg⟩] at hm
  generalize hdr : s.bitmaps.drop (w - 1).toNat = D at hm
  rcases D with _ | ⟨y, ys⟩
  · simp at hm
  have hidx : (w - 1).toNat < s.bitmaps.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hdr
    simp at hdr
  have hy : s.bitmaps[(w - 1).toNat] = y := by
    rw [List.drop_eq_getElem_cons hidx] at hdr
    simp only [List.cons.injEq] at hdr
    exact hdr.1
  simp only at hm
  generalize hbm : wordGenGcPartialMoveBitmap conf (y, stack, i, pa, curr, s.memory,
    s.mdomain, gs, rs) = R at hm
  rcases R with _ | ⟨hd1, ws, i2, pa2, m2, c2⟩
  · simp at hm
  simp only at hm
  have hc2 : c2 = true := by
    by_cases hmsb : y.msb = true
    · simp only [hmsb, not_true_eq_false, if_false] at hm
      split at hm
      · simp at hm
      · simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
        exact hm.2.2.2.2.2.1
    · simp only [hmsb, Bool.false_eq_true, not_false_eq_true, if_true, Option.some.injEq,
        Prod.mk.injEq] at hm
      exact hm.2.2.2.2.2
  subst hc2
  -- one `word_gen_gc_partial_move_bitmap_code` run on the loaded bitmap word
  let s2 : StackSemStateFiniteExact width C F := setVar 7 (.word y) s
  obtain ⟨ckB, q0, q1, q2, q5, q6, q7, hBbound, hB⟩ := genGcPartialMoveBitmapWordBoundedClock
    (init := init) (gs := gs) (rs := rs) y stack s2 i pa curr s.memory s.mdomain hd1 ws pa i2
    pa2 m2 old
    ⟨hbm, hsl, hws, hw2, hlen, hg, hshift, hcurr, huse, rfl, rfl, hus,
      by simp [s2, setVar, FUPDATE_HOL, h0], by simpa [s2, setVar, FUPDATE_HOL] using h1,
      by simpa [s2, setVar, FUPDATE_HOL] using h2, by simp [s2, getVar, setVar, FUPDATE_HOL, h3],
      by simp [s2, getVar, setVar, FUPDATE_HOL, h4], by simpa [s2, setVar, FUPDATE_HOL] using h5,
      by simpa [s2, setVar, FUPDATE_HOL] using h6, by simp [s2, getVar, setVar, FUPDATE_HOL],
      by simp [s2, getVar, setVar, FUPDATE_HOL, h8], hgs, hrs,
      by simp [s2, setVar, hst], hsp, by simpa [s2, setVar] using hbound⟩
  let s3 : StackSemStateFiniteExact width C F :=
    { s2 with
      memory := m2
      stack := init ++ old ++ hd1 ++ ws
      regs := s2.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa2), (4, .word i2),
        (5, q5), (6, q6), (7, q7),
        (8, .word (wordSemBytesInWord * BitVec.ofNat width (old ++ hd1).length))] }
  -- the state after one loop body
  let t : StackSemStateFiniteExact width C F :=
    setVar 0 (.word (y >>> (width - 1))) (setVar 9 (.word (w - 1 + 1)) (setVar 0 (.word y) s3))
  have h9c : s3.regs.lookup 9 = some (.word (w - 1)) := by
    simp [s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL, h9]
  have hpow : width < 2 ^ width := Nat.lt_two_pow_self
  have hm1 : (width - 1) % 2 ^ width = width - 1 := Nat.mod_eq_of_lt (by omega)
  have hl1 : ¬ width ≤ width - 1 := by omega
  have hbody : ∀ e, evaluate (.seq (.bitmapLoad 7 9) (.seq (wordGenGcPartialMoveBitmapCode conf)
      (.seq (.bitmapLoad 0 9) (.seq (add1Inst 9) (rightShiftInst 0 (width - 1))))),
      { s with clock := s.clock + (ckB + e) }) = (none, { t with clock := t.clock + e }) := by
    intro e
    have hadd := StackProps.evaluateAddClock e _ _ _ _ ⟨hB, by simp⟩
    have hs2 : setVar 7 (.word y) { s with clock := s.clock + (ckB + e) } =
        { { s2 with clock := s2.clock + ckB } with
          clock := { s2 with clock := s2.clock + ckB }.clock + e } := by
      simp only [s2, setVar]
      congr 1
      omega
    rw [evaluate_seq_none _ _ _ _ (bitmapLoad_eval { s with clock := s.clock + (ckB + e) } 7 9
        (w - 1) y hus (by decide) h9 hidx hy) le_rfl,
      hs2, evaluate_seq_none _ _ _ _ hadd (by simp [s2, setVar]),
      evaluate_seq_none _ _ _ _ (bitmapLoad_eval { s3 with clock := s3.clock + e } 0 9 (w - 1) y
        hus (by decide) h9c hidx hy) le_rfl]
    simp [evaluate_seq, evaluate_inst, add1Inst, rightShiftInst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, setVar, wordOpHOL, wordOp, fixClock,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordShiftHOL, hm1, hl1, t, s3, s2,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, h9]
  have hzz : (AndOp.and z z != (0 : BitVec width)) = true := by
    have : ¬ AndOp.and z z = (0 : BitVec width) := by
      change ¬ z &&& z = 0
      simpa using hz
    simpa [bne] using this
  have htc : t.clock = s.clock := rfl
  have hword : y.toNat * (2 ^ width + 1) ≤ 2 ^ width * (2 ^ width + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt y.isLt)
  have hdpos : 1 ≤ d := by omega
  by_cases hmsb : y.msb = true
  · simp only [hmsb, not_true_eq_false, if_false] at hm
    generalize hrec : wordGenGcPartialMoveBitmaps conf (.word (w + 1), ws, s.bitmaps, i2, pa2,
      curr, m2, s.mdomain, gs, rs) = R3 at hm
    rcases R3 with _ | ⟨hd3, st3, i3, pa3, m3, c3⟩
    · simp at hm
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.and_eq_true] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl⟩ := hm
    have hz' : y >>> (width - 1) ≠ 0 := word_msb_IFF_lsr_EQ_0.1 hmsb
    have hlenA := wordGenGcPartialMoveBitmaps_LENGTH hm0
    have hlenB := wordGenGcPartialMoveBitmaps_LENGTH hrec
    have hwn : w.toNat = (w - 1).toNat + 1 := by
      have h := BitVec.toNat_add (w - 1) 1
      rw [BitVec.sub_add_cancel] at h
      rw [h]
      have h1 : (1 : BitVec width).toNat = 1 := by
        simp [Nat.mod_eq_of_lt (show 1 < 2 ^ width by omega)]
      rw [h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hdec : t.bitmaps.length - (w + 1 - 1).toNat < d := by
      simp only [t, s3, s2, setVar, BitVec.add_sub_cancel]
      omega
    obtain ⟨ck', r0, r1, r2, r5, r6, r7, r9, hprev, hr⟩ := ih _ hdec (w + 1) ws (old ++ hd1) hd3
      st3 i2 pa2 curr i3 pa3 (y >>> (width - 1)) m3 t rfl hrec hblen
      (by simp [t, s3, s2, setVar, hcurr])
      huse hus
      (by simp [t, setVar, FUPDATE_HOL]) hz'
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, s3, setVar, FUPDATE_HOL, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL])
      (by simp [t, setVar, FUPDATE_HOL, BitVec.sub_add_cancel, BitVec.add_sub_cancel])
      (by simpa [t, s3, s2, setVar] using hgs) (by simpa [t, s3, s2, setVar] using hrs)
      (by simp [t, s3, setVar]) hsp
      (by
        have hl : (init ++ old ++ hd1 ++ ws).length = s.stack.length := by
          simp only [hst, List.length_append] at hlenA hlenB ⊢
          omega
        simp only [t, s3, s2, setVar]
        rw [hl]
        exact hbound)
    have hsum : (t.bitmaps.length - (w + 1 - 1).toNat) * (2 ^ width * (2 ^ width + 1) + 1) +
        (2 ^ width * (2 ^ width + 1) + 1) ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by
      have hh := Nat.mul_le_mul_right (2 ^ width * (2 ^ width + 1) + 1) (show t.bitmaps.length - (w + 1 - 1).toNat + 1 ≤ d by omega)
      simpa [Nat.add_mul] using hh
    have hbudget : ckB + ck' + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ckB + ck' + 1, r0, r1, r2, r5, r6, r7, r9, hbudget, ?_⟩
    rw [wordGenGcPartialMoveBitmapsCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hzz]
    rw [show ckB + ck' + 1 = ckB + (ck' + 1) by omega, hbody (ck' + 1)]
    have hmin : min (s.clock + (ckB + (ck' + 1))) (t.clock + (ck' + 1)) = t.clock + (ck' + 1) := by
      omega
    have hck : t.clock + (ck' + 1) ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock,
      ← wordGenGcPartialMoveBitmapsCode_eq]
    refine (congrArg (fun st => evaluate (wordGenGcPartialMoveBitmapsCode conf, st)) ?_).trans
      (hr.trans ?_)
    · congr 1
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
  · simp only [hmsb, Bool.false_eq_true, not_false_eq_true, if_true, Option.some.injEq,
      Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hm
    have hz0 : y >>> (width - 1) = 0 := by
      by_contra hne
      exact hmsb (word_msb_IFF_lsr_EQ_0.2 hne)
    have hsum : 2 ^ width * (2 ^ width + 1) + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by
      simpa using Nat.mul_le_mul_right (2 ^ width * (2 ^ width + 1) + 1) hdpos
    have hbudget : ckB + 1 ≤ d * (2 ^ width * (2 ^ width + 1) + 1) := by omega
    refine ⟨ckB + 1, .word (y >>> (width - 1)), q1, q2, q5, q6, q7, .word (w - 1 + 1), hbudget, ?_⟩
    rw [wordGenGcPartialMoveBitmapsCode_eq, evaluate_loop, evaluate_ite]
    simp only [getVar, HolRegImm.toWordRegImm, h0, StackSemStateOps.getVarImm, wordSemWordCmp,
      wordCmpHOL, hzz]
    rw [hbody 1]
    have hmin : min (s.clock + (ckB + 1)) (t.clock + 1) = t.clock + 1 := by omega
    have hck : t.clock + 1 ≠ 0 := by omega
    simp only [fixClock, contLoop, hmin, if_true, hck, if_false, decClock]
    have h00 : (AndOp.and (0#width) (0#width) != (0#width)) = false := by
      change (0#width &&& 0#width != 0#width) = false
      simp
    rw [evaluate_loop, evaluate_ite, evaluate_break]
    simp [getVar, StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, wordSemWordCmp, wordCmpHOL,
      fixClock, contLoop, StackSemControl.exitLoop, t, setVar, FUPDATE_HOL,
      HolFiniteMapExact.lookup_updateEq, hz0, h00]
    refine ⟨?_, by simp [s3, s2, setVar]⟩
    apply regs_ext
    intro k
    simp only [s3, s2, setVar, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
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
