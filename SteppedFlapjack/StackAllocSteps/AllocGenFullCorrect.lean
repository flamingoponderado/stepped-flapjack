import SteppedFlapjack.StackAllocSteps.GenMoveRootsCorrect
import SteppedFlapjack.StackAllocSteps.GenMoveCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational.Full
import SteppedFlapjack.StackAllocSteps.GenMoveLoopCorrect

/-! Bounded-clock correctness for full generational allocation. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalFull
open Flapjack.Compiler.Backend.StackRemove
set_option maxHeartbeats 4000000

theorem genGcMoveRootsWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init stack : List (WordLocW width)} :
    ∀ (bitmaps : List (BitVec width)) (s : StackSemStateFiniteExact width C F)
      (i pa ib pb curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (_new stack1 : List (WordLocW width))
      (_a1 i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcMoveRootsBitmaps conf (stack, bitmaps, i, pa, ib, pb, curr, m, dm) =
          (stack1, i1, pa1, ib1, pb1, m1, true) ∧
        bitmaps.length < 2 ^ width - 1 ∧ goodDimindex width ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.bitmaps = bitmaps ∧ s.useStack = true ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        getVar 9 s = some (holHd stack) ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r8, ∃ _r9 : WordLocW width, ∃ t0 t1,
        ck ≤ stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
        evaluate (wordGenGcMoveRootsBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ stack1
            clock := s.clock
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  rintro bitmaps s i pa ib pb curr m dm _ stack1 _ i1 pa1 ib1 pb1 m1 old
    ⟨hm, hblen, hg, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, rfl, hus, h0, h1, h2,
      h3, h4, h5, h6, h7, h8, h9, ht0, ht1, ht2, ht3, hst, hsp, hbound⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, t0, t1, hck, hr, rfl⟩ :=
    genGcMoveRootsBoundedClock hsl hws hw2 hlen hg hshift init _ stack rfl old stack1 i pa
      ib pb curr i1 pa1 ib1 pb1 m1 s hm hblen hcurr huse hus h0 h1 h2 (by simpa [getVar] using h3)
      (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
      (by simpa [getVar] using h9) ht0 ht1 ht2 ht3 hst hsp hbound
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, .word 0, t0, t1, hck, hr⟩


theorem genGcMoveLoopWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {c1 : Bool} :
    ∀ (k : Nat) (pax i pa ib pb pbx old : BitVec width)
      (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
      (i1 pa1 ib1 pb1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (tt : BitVec width) (s : StackSemStateFiniteExact width C F),
      wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, m, dm) =
          (i1, pa1, ib1, pb1, m1, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ (tt = 0 ↔ pbx = pb ∧ pax = pa) ∧
        (s.store.lookup (.temp 0)).isSome = true ∧ (s.store.lookup (.temp 1)).isSome = true ∧
        (s.store.lookup (.temp 5)).isSome = true ∧ (s.store.lookup (.temp 6)).isSome = true ∧
        s.store.lookup (.temp 2) = some (.word pb) ∧ s.store.lookup (.temp 3) = some (.word ib) ∧
        s.store.lookup (.temp 4) = some (.word pbx) ∧ (s.regs.lookup 0).isSome = true ∧
        getVar 1 s = some (.word pbx) ∧ getVar 2 s = some (.word pb) ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        getVar 7 s = some (.word tt) ∧ getVar 8 s = some (.word pax) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6, ck ≤ k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
        evaluate (wordGenGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb1),
              (.temp 3, .word ib1), (.temp 4, t4), (.temp 5, t5), (.temp 6, t6)]
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  rintro k pax i pa ib pb pbx old m dm i1 pa1 ib1 pb1 m1 tt s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, hstop,
      ht0, ht1, ht5, ht6, ht2, ht3, ht4, h0, h1, h2, h3, h4, h7, h8, h5, h6, -⟩
  exact genGcMoveLoopBoundedClock hsl hws hw2 hlen hshift old k s
    pax i pa ib pb pbx tt i1 pa1 ib1 pb1 m1 hm
    ⟨hcurr, huse, hstop, ht0, ht1, ht5, ht6, ht2, ht3, ht4, h0,
      by simpa [getVar] using h1, by simpa [getVar] using h2,
      by simpa [getVar] using h3, by simpa [getVar] using h4, h5, h6,
      by simpa [getVar] using h7, by simpa [getVar] using h8⟩


theorem genGcPartialMoveRootsWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {init stack : List (WordLocW width)} {gs rs : BitVec width} :
    ∀ (bitmaps : List (BitVec width)) (s : StackSemStateFiniteExact width C F)
      (i pa curr : BitVec width) (m : BitVec width → WordLocW width)
      (dm : BitVec width → Bool) (_new stack1 : List (WordLocW width))
      (_a1 i1 pa1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (old : List (WordLocW width)),
      wordGenGcPartialMoveRootsBitmaps conf (stack, bitmaps, i, pa, curr, m, dm, gs, rs) =
          (stack1, i1, pa1, m1, true) ∧
        bitmaps.length < 2 ^ width - 1 ∧ goodDimindex width ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word curr) ∧ s.useStore = true ∧
        s.memory = m ∧ s.mdomain = dm ∧ s.bitmaps = bitmaps ∧ s.useStack = true ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa) ∧ getVar 4 s = some (.word i) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word (wordSemBytesInWord * BitVec.ofNat width old.length)) ∧
        getVar 9 s = some (holHd stack) ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        s.stack = init ++ old ++ stack ∧ s.stackSpace = init.length ∧
        (width / 8) * s.stack.length < 2 ^ width →
      ∃ ck r0 r1 r2 r5 r6 r7 r8, ∃ _r9 : WordLocW width,
        ck ≤ stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveRootsBitmapsCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m1
            stack := init ++ old ++ stack1
            clock := s.clock
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
              (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  rintro bitmaps s i pa curr m dm _ stack1 _ i1 pa1 m1 old
    ⟨hm, hblen, hg, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, rfl, hus, h0, h1, h2,
      h3, h4, h5, h6, h7, h8, h9, hgs, hrs, hst, hsp, hbound⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, hr, rfl⟩ :=
    genGcPartialMoveRootsBoundedClock hsl hws hw2 hlen hg hshift init _ stack rfl old
      stack1 i pa curr i1 pa1 m1 s hm hblen hcurr huse hus h0 h1 h2 (by simpa [getVar] using h3)
      (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
      (by simpa [getVar] using h9) hgs hrs hst hsp hbound
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, .word 0, hck, hr⟩


theorem evaluate_full_first_move_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other curr : BitVec width}
    {ret glob moved : WordLocW width} {i pa ib pb : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (moved, i, pa, ib, pb, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullSetupState w len other ret glob s
    ∃ ck r0 r1 r2 r6 t0 t1,
      ck ≤ 2 ^ width ∧
      evaluate (wordGenGcMoveCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb), (.temp 3, .word ib)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  apply genGcMoveBoundedClock
  refine ⟨hm, hsl, hws, hw2, hlen, hshift, ?_, ?_, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [fullSetupState, getVar, setVar, setStore,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hc, hr, BitVec.add_comm]

open Flapjack.Compiler.Backend.StackRemove (leftShiftInst)


theorem evaluate_full_roots_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, ib, pb, curr, m, s.mdomain) =
      (stack1, i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 u0 u1,
      ck ≤ (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (wordGenGcMoveRootsBitmapsCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          store := S.store.updateListEq [(.temp 0, u0), (.temp 1, u1),
            (.temp 2, .word pb1), (.temp 3, .word ib1)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  have hframe := full_roots_frame_bound s hm
  dsimp only
  have H := genGcMoveRootsWordBoundedClock (conf := conf)
    (init := s.stack.take s.stackSpace) (stack := s.stack.drop s.stackSpace)
    s.bitmaps (fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s)
    i pa ib pb curr m s.mdomain [] stack1 0 i1 pa1 ib1 pb1 m1 []
  have HH := H (by
    refine ⟨hm, hb, hg, hsl, hws, hw2, hlen, hg, hshift, ?_⟩
    simp [fullRootsInputState, fullRootsSetupState, fullSetupState,
      getVar, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      hu, hus, hc, List.take_append_drop, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hframe), Nat.mul_comm, hs])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, u0, u1, hck, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, hck, by simpa using heval⟩


theorem evaluate_full_loop_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {k : Nat} {other i pa ib pb newEnd curr i1 pa1 ib1 pb1 : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf k (other, i, pa, ib, pb, newEnd, curr,
      s.memory, s.mdomain) = (i1, pa1, ib1, pb1, m, true))
    (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hp : s.regs.lookup 3 = some (.word pa)) (hi : s.regs.lookup 4 = some (.word i))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hib : s.store.lookup (.temp 3) = some (.word ib))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (he4 : s.store.lookup (.temp 4) = some (.word newEnd))
    (h0 : (s.regs.lookup 0).isSome = true) (h5 : (s.regs.lookup 5).isSome = true)
    (ht0 : (s.store.lookup (.temp 0)).isSome = true)
    (ht1 : (s.store.lookup (.temp 1)).isSome = true)
    (ht5 : (s.store.lookup (.temp 5)).isSome = true)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullLoopSetupState pa pb other newEnd s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
      ck ≤ k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (wordGenGcMoveLoopCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, t4),
            (.temp 5, t5), (.temp 6, t6)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  simp at ht0 ht1 ht5 hb hib he he4
  dsimp only
  apply genGcMoveLoopWordBoundedClock (conf := conf) (c1 := true)
    k other i pa ib pb newEnd curr s.memory s.mdomain i1 pa1 ib1 pb1 m
    ((pa - other) ||| (pb - newEnd))
  refine ⟨hm, hsl, hws, hw2, hlen, hls, hshift, ?_, ?_, rfl, rfl,
    full_loop_stop pa pb other newEnd, ?_⟩
  · simpa [fullLoopSetupState, setVar] using hc
  · simpa [fullLoopSetupState, setVar] using hu
  · simp [fullLoopSetupState, getVar, setVar, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, ht0, ht1, ht5, hb, hib, he, he4, h0, h5, hi, hp]


theorem evaluate_full_move_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other curr : BitVec width}
    {ret glob moved : WordLocW width} {i pa ib pb : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true) (hr : s.regs.lookup 0 = some ret)
    (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (moved, i, pa, ib, pb, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullSetupState w len other ret glob s
    ∃ ck r0 r1 r2 r6 t0 t1,
      ck ≤ 2 ^ width ∧
      evaluate (listSeqHOL (fullSetupCode ++ [wordGenGcMoveCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb), (.temp 3, .word ib)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r6, t0, t1, hck, hrun⟩ := evaluate_full_first_move_bounded
    (w := w) (len := len) (other := other) (ret := ret) s hu hr hc hm hsl hws hw2 hlen hshift
  refine ⟨ck, r0, r1, r2, r6, t0, t1, hck, ?_⟩
  rw [evaluate_full_setup_append [wordGenGcMoveCode conf] (by simp)
    { s with clock := s.clock + ck } hu hr hw hl ho hg hws]
  simpa only [listSeqHOL, fullSetupState, setVar, setStore] using hrun


theorem evaluate_full_roots_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, ib, pb, curr, m, s.mdomain) =
      (stack1, i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := fullSetupState w len other ret glob s
    let M := { B with
      memory := m
      store := B.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
        (.temp 2, .word pb), (.temp 3, .word ib)]
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := fullRootsInputState conf w len other moved i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 u0 u1,
      ck ≤ (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]),
        { M with clock := M.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          store := S.store.updateListEq [(.temp 0, u0), (.temp 1, u1),
            (.temp 2, .word pb1), (.temp 3, .word ib1)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  dsimp only
  have hframe := full_roots_frame_bound s hm
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, hck, hrun⟩ := evaluate_full_roots_bounded
    (w := w) (len := len) (other := other) (moved := moved) (ret := ret) (glob := glob)
    (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6) (t0 := t0) (t1 := t1)
    s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, u0, u1, hck, ?_⟩
  rw [evaluate_full_roots_prepare_append (moved := moved) (other := other)
    [wordGenGcMoveRootsBitmapsCode conf] (by simp) _
    (by simpa [fullSetupState, setVar, setStore] using hu)
    (by simpa [fullSetupState, setVar, setStore] using hus)
    (by simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simpa [fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
    (by simp [fullSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simpa [fullSetupState, setVar, setStore] using hframe) hsl hws]
  simpa only [listSeqHOL, fullRootsInputState, fullRootsSetupState, fullSetupState,
    setVar, setStore] using hrun


theorem evaluate_full_loop_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {k : Nat} {other i pa ib pb newEnd curr i1 pa1 ib1 pb1 : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf k (other, i, pa, ib, pb, newEnd, curr,
      s.memory, s.mdomain) = (i1, pa1, ib1, pb1, m, true))
    (hu : s.useStore = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hp : s.regs.lookup 3 = some (.word pa)) (hi : s.regs.lookup 4 = some (.word i))
    (hb : s.store.lookup (.temp 2) = some (.word pb))
    (hib : s.store.lookup (.temp 3) = some (.word ib))
    (he : s.store.lookup (.temp 6) = some (.word newEnd))
    (he4 : s.store.lookup (.temp 4) = some (.word newEnd))
    (h0 : (s.regs.lookup 0).isSome = true) (h5 : (s.regs.lookup 5).isSome = true)
    (ht0 : (s.store.lookup (.temp 0)).isSome = true)
    (ht1 : (s.store.lookup (.temp 1)).isSome = true)
    (ht5 : (s.store.lookup (.temp 5)).isSome = true)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := fullLoopSetupState pa pb other newEnd s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6,
      ck ≤ k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          store := S.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, t4),
            (.temp 5, t5), (.temp 6, t6)]
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hck, hrun⟩ :=
    evaluate_full_loop_bounded s hm hu hc hp hi hb hib he he4 h0 h5 ht0 ht1 ht5
      hsl hws hw2 hlen hls hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hck, ?_⟩
  rw [evaluate_full_loop_setup_append [wordGenGcMoveLoopCode conf] (by simp)
    { s with clock := s.clock + ck } hu hp hb he ho]
  simpa only [listSeqHOL, fullLoopSetupState, setVar] using hrun


theorem evaluate_full_loop_list_after_roots_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width}
    {m0 m m1 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    let S := fullLoopSetupState pa pb other (other + len) R
    ∃ ck v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6,
      ck ≤ (len >>> wordShiftAmount width).toNat * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m1
          store := S.store.updateListEq [(.temp 0, z0), (.temp 1, z1),
            (.temp 2, .word pb1), (.temp 3, .word ib1), (.temp 4, z4),
            (.temp 5, z5), (.temp 6, z6)]
          regs := S.regs.updateListEq [(0, v0), (1, v1), (2, v2), (3, .word pa1),
            (4, .word i1), (5, v5), (6, v6), (7, v7), (8, v8)] }) := by
  dsimp only
  apply evaluate_full_loop_with_prefix_bounded
  · exact hm
  all_goals first | assumption | simp [fullRootsOutputState, fullRootsInputState, fullRootsSetupState,
    fullSetupState, setVar, setStore, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    hu, BitVec.add_comm]


theorem evaluate_full_loop_tail_after_roots_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i1 pa1 ib1 pb1 : BitVec width}
    {ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 : WordLocW width}
    {m0 m m1 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hg : goodDimindex width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width)
    (hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
      ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
    ∃ ck v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p7 p1 p4,
      let L := fullLoopOutputState i1 pa1 ib1 pb1
        v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1
        (fullLoopSetupState pa pb other (other + len) R)
      let S := fullCleanupState curr other pa1 pb1 ret L
      let T := { S with
        regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
        store := S.store.updateEq (.triggerGC, .word (pa1 + newTrig (pb1 - pa1) w genSizes)) }
      let C := fullClearState T
      let trigger := pa1 + newTrig (pb1 - pa1) w genSizes
      let V := setVar 2 (.word (trigger - pa1)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      ck ≤ (len >>> wordShiftAmount width).toNat * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++
        fullTailCode genSizes), { R with clock := R.clock + ck }) =
        if (trigger - pa1).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  dsimp only
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  let B := fullLoopSetupState pa pb other (other + len) R
  obtain ⟨ck, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, hck, hloop⟩ :=
    evaluate_full_loop_list_after_roots_bounded (w := w) (moved := moved)
      (i0 := i0) (pa0 := pa0) (ib0 := ib0) (pb0 := pb0)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      (t0 := t0) (t1 := t1) (r0 := r0) (r1 := r1) (r2 := r2) (r5 := r5)
      (r6 := r6) (r7 := r7) (r8 := r8) (u0 := u0) (u1 := u1) (m0 := m0)
      (roots := roots) s hm hu hc ho hsl hws hw2 hlen hls hshift
  obtain ⟨p7, p1, p4, htail⟩ := evaluate_full_cleanup_after_loop
    (curr := curr) (other := other) (pa := pa1) (pb := pb1) (w := w) (ret := ret)
    genSizes i1 ib1 v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1 B hg
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore] using hu)
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hc)
    (by simpa [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
    (by simp [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [B, R, fullLoopSetupState, fullRootsOutputState, fullRootsInputState,
      fullRootsSetupState, fullSetupState, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
  refine ⟨ck, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, hck, ?_⟩
  let L := fullLoopOutputState i1 pa1 ib1 pb1
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m1 B
  have hloop' : evaluate (listSeqHOL (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]),
    { R with clock := R.clock + ck }) = (none, L) := hloop
  rw [AllocGenerationalPartial.evaluate_listSeq_append_collector
    (fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) (fullTailCode genSizes)
    _ L (by simp) (by simp [fullTailCode])
    (fun x hx V => full_loop_prefix_clock conf x hx V)
    (by simp [L, B, fullLoopOutputState, fullLoopSetupState, setVar]) hloop']
  simpa only [fullTailCode, L, B, R] using htail


theorem evaluate_full_program_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width}
    {ret glob : WordLocW width}
    {m0 m m3 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (.word moved, i0, pa0, ib0, pb0, m0, true))
    (hrts : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, ib0, pb0, curr, m0, s.mdomain) =
      (roots, i, pa, ib, pb, m, true))
    (hloop : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i3, pa3, ib3, pb3, m3, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hglob : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1,
      let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
        ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
      ∃ v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p7 p1 p4,
      let L := fullLoopOutputState i3 pa3 ib3 pb3
        v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
        (fullLoopSetupState pa pb other (other + len) R)
      let S := fullCleanupState curr other pa3 pb3 ret L
      let T := { S with
        regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
        store := S.store.updateEq (.triggerGC, .word (pa3 + newTrig (pb3 - pa3) w genSizes)) }
      let C := fullClearState T
      let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
      let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
        (setVar 1 (.word w) C))
      ck ≤ 2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (fullProgramCode conf genSizes),
        { s with clock := s.clock + ck }) =
        if (trigger - pa3).toNat < w.toNat then
          (some (.halt (.word 1)), emptyEnv C) else (none, V) := by
  obtain ⟨a, q0, q1, q2, q6, t0, t1, ha, hmove⟩ :=
    evaluate_full_move_with_prefix_bounded s hu hr hw hl ho hglob hc hm hsl hws hw2 hlen hshift
  obtain ⟨b, r0, r1, r2, r5, r6, r7, r8, u0, u1, hbnd, hroots⟩ :=
    evaluate_full_roots_with_prefix_bounded (w := w) (len := len) (moved := moved)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2)
      (q6 := q6) (t0 := t0) (t1 := t1)
      s hrts hu hus hc ho hb hs hsl hws hw2 hlen hg hshift
  let B := fullSetupState w len other ret glob s
  let M := { B with
    memory := m0
    store := B.store.updateListEq [(.temp 0, t0), (.temp 1, t1),
      (.temp 2, .word pb0), (.temp 3, .word ib0)]
    regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa0), (4, .word i0), (5, .word moved), (6, q6)] }
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  obtain ⟨c, v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, hcnd, htail⟩ :=
    evaluate_full_loop_tail_after_roots_bounded (w := w) (moved := moved)
      (i0 := i0) (pa0 := pa0) (ib0 := ib0) (pb0 := pb0)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      (t0 := t0) (t1 := t1) (r0 := r0) (r1 := r1) (r2 := r2) (r5 := r5)
      (r6 := r6) (r7 := r7) (r8 := r8) (u0 := u0) (u1 := u1) (m0 := m0)
      (roots := roots) genSizes s hloop hu hc ho hg hsl hws hw2 hlen hls hshift
  have hb' : b ≤ s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) :=
    hbnd.trans (Nat.mul_le_mul_right _ (by simp))
  have hc' : c ≤ 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) :=
    hcnd.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (BitVec.isLt _)))
  have hbudget : a + (b + c) ≤ 2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by omega
  refine ⟨a + (b + c), q0, q1, q2, q6, t0, t1, r0, r1, r2, r5, r6, r7, r8, u0, u1,
    v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, hbudget, ?_⟩
  unfold fullProgramCode
  apply evaluate_full_collector_clocks_pair
    (fullSetupCode ++ [wordGenGcMoveCode conf])
    ((fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf]) ++
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ fullTailCode genSizes))
    (by simp) (by simp) s M a (b + c)
  · exact fun x hx V => full_move_prefix_clock conf x hx V
  · rfl
  · exact hmove
  · apply evaluate_full_collector_clocks_pair
      (fullRootsPrepareCode conf ++ [wordGenGcMoveRootsBitmapsCode conf])
      ((fullLoopPrepareCode ++ [wordGenGcMoveLoopCode conf]) ++ fullTailCode genSizes)
      (by simp) (by simp) M R b c
    · exact fun x hx V => full_roots_prefix_clock conf x hx V
    · rfl
    · exact hroots
    · exact htail


theorem evaluate_full_program_source_result_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w len other moved curr i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3 : BitVec width}
    {ret glob : WordLocW width}
    {m0 m m3 : BitVec width → WordLocW width} {roots : List (WordLocW width)}
    (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcMove conf (glob, 0, other, len >>> wordShiftAmount width,
      other + len, curr, s.memory, s.mdomain) = (.word moved, i0, pa0, ib0, pb0, m0, true))
    (hrts : wordGenGcMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i0, pa0, ib0, pb0, curr, m0, s.mdomain) =
      (roots, i, pa, ib, pb, m, true))
    (hloop : wordGenGcMoveLoop conf (len >>> wordShiftAmount width).toNat
      (other, i, pa, ib, pb, other + len, curr, m, s.mdomain) =
      (i3, pa3, ib3, pb3, m3, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hl : s.store.lookup .heapLength = some (.word len))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hglob : s.store.lookup .globals = some glob)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let source := { s with
      memory := m3
      stack := s.stack.take s.stackSpace ++ roots
      store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
      regs := HolFiniteMapExact.empty }
    let short := ((pa3 + newTrig (pb3 - pa3) w genSizes) - pa3).toNat < w.toNat
    let result := if short then some (.halt (.word 1)) else none
    let target := if short then emptyEnv source else source
    ∃ ck l2,
      ck ≤ 2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (fullProgramCode conf genSizes),
        { s with clock := s.clock + ck }) = (result, { target with regs := l2 }) ∧
      (result ≠ none → result = some (.halt (.word 1))) ∧
      target.regs.submap l2 ∧ (result = none → l2.lookup 0 = some ret) := by
  obtain ⟨ck, q0, q1, q2, q6, t0, t1, r0, r1, r2, r5, r6, r7, r8, u0, u1,
    v0, v1, v2, v5, v6, v7, v8, z0, z1, z4, z5, z6, p7, p1, p4, hck, heval⟩ :=
    evaluate_full_program_bounded genSizes s hm hrts hloop hu hus hr hw hl ho hglob hc hb hs
      hsl hws hw2 hlen hls hg hshift
  let R := fullRootsOutputState conf w len other moved i0 pa0 ib0 pb0 i pa ib pb
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1 m0 m roots s
  let L := fullLoopOutputState i3 pa3 ib3 pb3
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 m3
    (fullLoopSetupState pa pb other (other + len) R)
  let S := fullCleanupState curr other pa3 pb3 ret L
  let trigger := pa3 + newTrig (pb3 - pa3) w genSizes
  let T := { S with
    regs := ((S.regs.updateEq (1, p1)).updateEq (7, p7)).updateEq (4, p4)
    store := S.store.updateEq (.triggerGC, .word trigger) }
  let C := fullClearState T
  let V := setVar 2 (.word (trigger - pa3)) (setVar 2 (.word trigger)
    (setVar 1 (.word w) C))
  let source := { s with
    memory := m3
    stack := s.stack.take s.stackSpace ++ roots
    store := fullSourceStore conf genSizes w curr other moved pa3 pb3 s.store
    regs := HolFiniteMapExact.empty }
  have hstate := full_final_state conf genSizes w len curr other moved
    i0 pa0 ib0 pb0 i pa ib pb i3 pa3 ib3 pb3
    ret glob q0 q1 q2 q6 t0 t1 r0 r1 r2 r5 r6 r7 r8 u0 u1
    v0 v1 v2 v5 v6 v7 v8 z0 z1 z4 z5 z6 p1 p7 p4 m0 m m3 roots s
  have hn : V = { source with regs := V.regs } := hstate.1
  have hh : emptyEnv C = emptyEnv source := hstate.2.1
  have hret : V.regs.lookup 0 = some ret := hstate.2.2
  have heval' : evaluate (listSeqHOL (fullProgramCode conf genSizes),
      { s with clock := s.clock + ck }) =
      if (trigger - pa3).toNat < w.toNat then
        (some (.halt (.word 1)), emptyEnv C) else (none, V) := heval
  dsimp only
  by_cases hshort : (trigger - pa3).toNat < w.toNat
  · simp only [trigger] at hshort heval'
    simp only [hshort, if_true] at heval' ⊢
    refine ⟨ck, HolFiniteMapExact.empty, hck, ?_, by simp, ?_, by simp⟩
    · exact heval'.trans (congrArg (fun state => (some (StackSemResult.halt (WordLocW.word (1 : BitVec width))), state)) hh)
    · exact AllocGenerationalPartial.partial_empty_regs_submap _
  · simp only [trigger] at hshort heval'
    simp only [hshort, if_false] at heval' ⊢
    refine ⟨ck, V.regs, hck, ?_, by simp, ?_, ?_⟩
    · exact heval'.trans (congrArg (fun state => ((none : Option (StackSemResult width)), state)) hn)
    · exact AllocGenerationalPartial.partial_empty_regs_submap _
    · exact fun _ => hret


/-- Full generational allocation correctness with a concrete clock allowance. -/
theorem alloc_correct_lemma_Generational_full_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    (hp : ¬wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    ∃ ck l2,
      ck ≤ 2 ^ width + s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + 2 ^ width * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (wordGcCode conf, { s with
        useStore := true
        useStack := true
        useAlloc := false
        clock := s.clock + ck
        regs := l
        gcFun := anything
        code := sptFromAList (compile c (sptToAList s.code)) }) =
        (r, { t with
          useStore := true
          useStack := true
          useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code))
          regs := l2
          gcFun := anything }) ∧
      (r ≠ none → r = some (.halt (.word 1))) ∧
      t.regs.submap l2 ∧ (r = none → l2.lookup 0 = some ret) := by
  let A := setStore .allocSize (.word w) s
  let curr := wordSemTheWord (holFapply A.store .currHeap)
  let other := wordSemTheWord (holFapply A.store .otherHeap)
  let len := wordSemTheWord (holFapply A.store .heapLength)
  let trig := wordSemTheWord (holFapply A.store .triggerGC)
  let endh := wordSemTheWord (holFapply A.store .endOfHeap)
  let globalWord := wordSemTheWord (holFapply A.store .globals)
  obtain ⟨moved, i0, pa0, ib0, pb0, m0, roots, i, pa, ib, pb, m,
    i3, pa3, ib3, pb3, m3, hm, hrts, hloop, hass, hsource⟩ :=
    alloc_full_source_result ha hr hgc hk hp
  obtain ⟨loads, hgood, hlen, hls, hsl⟩ := AllocGenerationalPartial.partial_source_loads conf A.store hass
  have load : ∀ key ∈ ([.globals, .currHeap, .otherHeap, .heapLength, .triggerGC,
      .genStart, .endOfHeap] : List WordStoreHOL),
      s.store.lookup key = some (.word (wordSemTheWord (holFapply A.store key))) := by
    intro key hkey
    have h := loads key hkey
    have hne : key ≠ .allocSize := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hkey
      rcases hkey with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hne] using h
  have hc := load .currHeap (by simp)
  have ho := load .otherHeap (by simp)
  have hl := load .heapLength (by simp)
  have ht := load .triggerGC (by simp)
  have he := load .endOfHeap (by simp)
  have hglob := load .globals (by simp)
  rw [holFapply_of_lookup (loads .globals (by simp))] at hm
  have hws : wordShiftAmount width < width := by
    unfold wordShiftAmount
    rcases hgood with h | h <;> simp [h]
  have hw2 : 2 < width := by rcases hgood with h | h <;> omega
  have hshift : ∀ x : BitVec width, x <<< wordShiftAmount width = x * wordSemBytesInWord := by
    intro x
    rw [← bytesInWord_mul_eq_shift x hgood, BitVec.mul_comm]
  let R : StackSemStateFiniteExact width C F := { s with
    useStore := true
    useStack := true
    useAlloc := false
    regs := l
    gcFun := anything
    code := sptFromAList (compile c (sptToAList s.code)) }
  let P := setVar 7 (.word (endh - trig)) (setVar 7 (.word endh) (setVar 8 (.word trig) R))
  obtain ⟨ck, l2, hck, hrun, hhalt, hsub, hret⟩ := evaluate_full_program_source_result_bounded genSizes P
    hm hrts hloop rfl rfl
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl0)
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl1)
    hl ho hglob hc hbl hstack hsl hws hw2 hlen hls hgood hshift
  dsimp only at hrun hhalt hsub hret hsource
  let short := ((pa3 + newTrig (pb3 - pa3) w genSizes) - pa3).toNat < w.toNat
  have hrResult : r = (if short then some (.halt (.word 1)) else none) := by
    by_cases h : short <;> simp only [short] at h ⊢ <;>
      simp only [h, if_true, if_false, Prod.mk.injEq] at hsource ⊢ <;> exact hsource.1
  have hstate : { (if short then emptyEnv { P with
        memory := m3
        stack := P.stack.take P.stackSpace ++ roots
        store := fullSourceStore conf genSizes w curr other moved pa3 pb3 P.store
        regs := HolFiniteMapExact.empty } else { P with
        memory := m3
        stack := P.stack.take P.stackSpace ++ roots
        store := fullSourceStore conf genSizes w curr other moved pa3 pb3 P.store
        regs := HolFiniteMapExact.empty }) with regs := l2 } =
      { t with
        useStore := true
        useStack := true
        useAlloc := false
        code := sptFromAList (compile c (sptToAList s.code))
        regs := l2
        gcFun := anything } := by
    by_cases h : short
    · simp only [short] at h
      simp only [h, if_true, Prod.mk.injEq] at hsource
      rw [hsource.2]
      simp only [short, h, if_true]
      rfl
    · simp only [short] at h
      simp only [h, if_false, Prod.mk.injEq] at hsource
      rw [hsource.2]
      simp only [short, h, if_false]
      rfl
  have htregs : t.regs = HolFiniteMapExact.empty := by
    by_cases h : short <;> simp only [short] at h <;>
      simp only [h, if_true, if_false, Prod.mk.injEq] at hsource <;>
      rw [hsource.2]
    all_goals rfl
  refine ⟨ck, l2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P, R, setVar] using hck
  · simp only [wordGcCode, hk]
    rw [evaluate_full_select_from_source conf genSizes w _ _
      { R with clock := s.clock + ck } hass hp rfl hl1]
    rw [holFapply_of_lookup ht, holFapply_of_lookup he]
    simp only [wordSemTheWord]
    have hrunFinal := hrun.trans (congrArg
      (fun U => ((if short then some (StackSemResult.halt (WordLocW.word (1 : BitVec width))) else none), U)) hstate)
    rw [← hrResult] at hrunFinal
    simpa only [fullProgramCode, fullSetupCode, fullRootsPrepareCode,
      fullLoopPrepareCode, fullTailCode, List.cons_append, List.nil_append,
      P, R, setVar, trig, endh, wordSemTheWord] using hrunFinal
  · rw [hrResult]
    exact hhalt
  · rw [htregs]
    exact AllocGenerationalPartial.partial_empty_regs_submap _
  · rw [hrResult]
    exact hret


end SteppedFlapjack.StackAllocSteps
