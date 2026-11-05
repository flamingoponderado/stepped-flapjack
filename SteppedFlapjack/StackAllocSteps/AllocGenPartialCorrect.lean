import SteppedFlapjack.StackAllocSteps.AllocGenFullCorrect
import SteppedFlapjack.StackAllocSteps.GenMoveDataCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.AllocGenerational.Partial

/-! Bounded-clock correctness for partial generational allocation. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackAlloc.AllocGenerationalPartial
open Flapjack.Compiler.Backend.StackRemove
set_option maxHeartbeats 4000000

theorem genGcPartialRefsWordBoundedClock {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {gs rs : BitVec width} :
    ∀ (k : Nat) (r2a1 r1a1 _r2a2 i1 pa1 _ib1 _pb1 old1 : BitVec width)
      (m1 : BitVec width → WordLocW width) (dm1 : BitVec width → Bool) (_c1 : Bool)
      (i2 pa2 _ib2 _pb2 : BitVec width) (m2 : BitVec width → WordLocW width)
      (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveRefList k conf (r1a1, i1, pa1, old1, m1, dm1, true, gs, rs, r2a1) =
          (i2, pa2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧ goodDimindex width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧ s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true ∧ (s.regs.lookup 6).isSome = true ∧
        (s.regs.lookup 7).isSome = true ∧
        getVar 8 s = some (.word r1a1) ∧ getVar 9 s = some (.word r2a1) →
      ∃ ck r0 r1 r2 r5 r6 r7 r8 r9, ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveRefListCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  rintro k r2a1 r1a1 _ i1 pa1 _ _ old1 m1 dm1 _ i2 pa2 _ _ m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hg, hshift, hcurr, huse, rfl, rfl, hgs, hrs, h0, h1, h2, h3, h4,
      h5, h6, h7, h8, h9⟩
  exact genGcPartialMoveRefListBoundedClock hsl hws hw2 hlen hg hshift r2a1 old1 k r1a1 i1 pa1
    true i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
    (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
    (by simpa [getVar] using h9)


theorem genGcPartialDataWordBoundedClock {width : Nat} [NeZero width]
    {C F D E : Type} [Nonempty D] [Nonempty E]
    {conf : Config} {gs rs : BitVec width} :
    ∀ (k : Nat) (ha1 i1 pa1 old1 : BitVec width) (m1 : BitVec width → WordLocW width)
      (dm1 : BitVec width → Bool) (c1 : Bool) (i2 pa2 : BitVec width)
      (m2 : BitVec width → WordLocW width) (s : StackSemStateFiniteExact width C F),
      wordGenGcPartialMoveData conf k (ha1, i1, pa1, old1, m1, dm1, gs, rs) =
          (i2, pa2, m2, true) ∧
        shiftLength conf < width ∧ wordShiftAmount width < width ∧ 2 < width ∧
        conf.lenSize ≠ 0 ∧ conf.lenSize + 2 < width ∧
        (∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord) ∧
        s.store.lookup .currHeap = some (.word old1) ∧ s.useStore = true ∧
        s.memory = m1 ∧ s.mdomain = dm1 ∧ goodDimindex width ∧
        s.store.lookup (.temp 0) = some (.word gs) ∧
        s.store.lookup (.temp 1) = some (.word rs) ∧
        (s.regs.lookup 0).isSome = true ∧ (s.regs.lookup 1).isSome = true ∧
        (s.regs.lookup 2).isSome = true ∧
        getVar 3 s = some (.word pa1) ∧ getVar 4 s = some (.word i1) ∧
        (s.regs.lookup 5).isSome = true →
      (s.regs.lookup 6).isSome = true →
      (s.regs.lookup 7).isSome = true →
      getVar 8 s = some (.word ha1) ∧ c1 = true →
      ∃ ck r0 r1 r2 r5 r6 r7, ∃ (_t0 : D) (_t1 : E), ck ≤ k * (2 ^ width * (2 ^ width + 1) + 1) ∧
        evaluate (wordGenGcPartialMoveDataCode conf, { s with clock := s.clock + ck }) =
          (none, { s with
            memory := m2
            regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
              (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  rintro k ha1 i1 pa1 old1 m1 dm1 c1 i2 pa2 m2 s
    ⟨hm, hsl, hws, hw2, hlen, -, hshift, hcurr, huse, rfl, rfl, hg, hgs, hrs,
      h0, h1, h2, h3, h4, h5⟩ h6 h7 ⟨h8, -⟩
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hck, he⟩ :=
    genGcPartialMoveDataBoundedClock hsl hws hw2 hlen hg hshift old1 gs rs k ha1 i1 pa1
      i2 pa2 m2 s hm hcurr huse hgs hrs h0 h1 h2 (by simpa [getVar] using h3)
      (by simpa [getVar] using h4) h5 h6 h7 (by simpa [getVar] using h8)
  obtain ⟨t0⟩ := ‹Nonempty D›
  obtain ⟨t1⟩ := ‹Nonempty E›
  exact ⟨ck, r0, r1, r2, r5, r6, r7, t0, t1, hck, he⟩


theorem evaluate_partial_first_move_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob moved : WordLocW width} {i pa : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (moved, i, pa, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := setupState w gs endh curr len other ret glob s
    ∃ ck r0 r1 r2 r6,
      ck ≤ 2 ^ width ∧
      evaluate (wordGenGcPartialMoveCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  apply genGcPartialMoveBoundedClock
  refine ⟨hm, hsl, hws, hw2, hlen, hshift, ?_, ?_, rfl, rfl, hgood,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [setupState, getVar, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL, hu, hc, hr, hw]

open Flapjack.Compiler.Backend.StackRemove (leftShiftInst constInst)


theorem evaluate_partial_roots_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8,
      ck ≤ (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (wordGenGcPartialMoveRootsBitmapsCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  have hframe := partial_roots_frame_bound s hm
  dsimp only
  have H := genGcPartialMoveRootsWordBoundedClock (conf := conf) (gs := gs) (rs := endh - curr)
    (init := s.stack.take s.stackSpace) (stack := s.stack.drop s.stackSpace)
    s.bitmaps (rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s)
    i pa curr m s.mdomain [] stack1 0 i1 pa1 m1 []
  have HH := H (by
    refine ⟨hm, hb, hg, hsl, hws, hw2, hlen, hg, hshift, ?_⟩
    simp [rootsInputState, rootsSetupState, setupState, getVar, setVar, setStore,
      HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL,
      HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hus, hc,
      List.take_append_drop, List.length_take, Nat.min_eq_left (Nat.le_of_lt hframe),
      Nat.mul_comm, hs])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, r8, hck, by simpa using heval⟩


theorem evaluate_partial_refs_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) ∧
      evaluate (wordGenGcPartialMoveRefListCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  dsimp only
  apply genGcPartialRefsWordBoundedClock (conf := conf) (gs := gs) (rs := rs)
    (2 ^ width) (curr + len) endh 0 i pa 0 0 curr m s.mdomain true i2 pa2 0 0 m2
  refine ⟨hm, hsl, hws, hw2, hlen, hls, hg, hshift, ?_⟩
  simp [refsInputState, getVar, setVar, HolFiniteMapExact.lookup_updateListEq,
    FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    hu, hc, BitVec.add_comm]
  exact ⟨hgs, hrs⟩


theorem evaluate_partial_data_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 : BitVec width → WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
    ∃ ck r0 r1 r2 r5 r6 r7,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) ∧
      evaluate (wordGenGcPartialMoveDataCode conf, { S with clock := S.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  dsimp only
  have H := genGcPartialDataWordBoundedClock (conf := conf) (gs := gs) (rs := rs)
    (D := Unit) (E := Unit) (2 ^ width) other i pa curr m s.mdomain true i2 pa2 m2
    (dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s)
  have HH := H (by
    refine ⟨hm, hsl, hws, hw2, hlen, hls, hshift, ?_⟩
    simp [dataInputState, getVar, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hu, hc, hg]
    exact ⟨hgs, hrs⟩)
    (by simp [dataInputState, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [dataInputState, setVar, HolFiniteMapExact.lookup_updateListEq,
      FUPDATE_LIST_HOL, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
    (by simp [dataInputState, getVar, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, t0, t1, hck, heval⟩ := HH
  exact ⟨ck, r0, r1, r2, r5, r6, r7, hck, heval⟩


theorem evaluate_partial_setup_move_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other : BitVec width}
    {ret glob moved : WordLocW width} {i pa : BitVec width}
    {m : BitVec width → WordLocW width} (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (moved, i, pa, m, true))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let S := setupState w gs endh curr len other ret glob s
    ∃ ck r0 r1 r2 r6,
      ck ≤ 2 ^ width ∧
      evaluate (listSeqHOL (partialSetupCode ++ [wordGenGcPartialMoveCode conf]),
        { s with clock := s.clock + ck }) =
        (none, { S with
          memory := m
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2),
            (3, .word pa), (4, .word i), (5, moved), (6, r6)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r6, hck, hrun⟩ :=
    evaluate_partial_first_move_bounded s hu hr hw hc hm hsl hws hw2 hlen hgood hshift
  refine ⟨ck, r0, r1, r2, r6, hck, ?_⟩
  rw [evaluate_partial_setup_append [wordGenGcPartialMoveCode conf] (by simp)
    { s with clock := s.clock + ck } hu hr hw hgs he hc hl hg ho hws]
  simpa only [listSeqHOL, setupState, setVar, setStore] using hrun


theorem evaluate_partial_roots_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := setupState w gs endh curr len other ret glob s
    let M := { B with
      memory := m
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck r0 r1 r2 r5 r6 r7 r8,
      ck ≤ (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ∧
      evaluate (listSeqHOL (partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]), { M with clock := M.clock + ck }) =
        (none, { S with
          memory := m1
          stack := s.stack.take s.stackSpace ++ stack1
          clock := S.clock
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
            (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, hck, hrun⟩ :=
    evaluate_partial_roots_bounded (w := w) (len := len) (other := other) (moved := moved)
      (ret := ret) (glob := glob) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, hck, ?_⟩
  rw [evaluate_partial_roots_prepare_append (moved := moved) (curr := curr)
    (gs := gs) (rs := endh - curr) (i := i) (pa := pa) (i1 := i1) (pa1 := pa1)
    (m := m) (m1 := m1) (stack1 := stack1) _ (by simp) _
    (by simpa [setupState, setVar, setStore] using hu)
    (by simpa [setupState, setVar, setStore] using hus)
    (by simp [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    (by simpa [setupState, setVar, setStore, HolFiniteMapExact.lookup_updateEq,
      FUPDATE_HOL] using hc) hsl hws
    (by simpa [setupState, setVar, setStore] using hm)]
  simpa only [listSeqHOL, rootsInputState, rootsSetupState, setupState, setVar, setStore]
    using hrun


theorem evaluate_partial_refs_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      stack := stack
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
    ∃ ck r0 r1 r2 r5 r6 r7 r8 r9,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) ∧
      evaluate (listSeqHOL [.get 8 .currHeap, .get 9 .heapLength,
        addInst 9 8, .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf],
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, hrun⟩ :=
    evaluate_partial_refs_bounded (q0 := q0) (q1 := q1) (q2 := q2) (q5 := q5)
      (q6 := q6) (q7 := q7) (q8 := q8) (stack := stack)
      s hm hu hc hgs hrs hsl hws hw2 hlen hls hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, r8, r9, hck, ?_⟩
  rw [show ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
    .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] : List (HolProg width)) =
    [.get 8 .currHeap, .get 9 .heapLength, addInst 9 8, .get 8 .endOfHeap] ++
      [wordGenGcPartialMoveRefListCode conf] from rfl]
  rw [evaluate_partial_refs_setup_append (curr := curr) (len := len) (endh := endh)
    _ (by simp) { s with
      memory := m
      stack := stack
      clock := s.clock + ck
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    hu hc hl he]
  simpa only [listSeqHOL, refsInputState, setVar] using hrun


theorem evaluate_partial_data_with_prefix_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 : BitVec width → WordLocW width}
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }
    let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
    ∃ ck r0 r1 r2 r5 r6 r7,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) ∧
      evaluate (listSeqHOL [.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf],
        { R with clock := R.clock + ck }) =
        (none, { S with
          memory := m2
          regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
            (4, .word i2), (5, r5), (6, r6), (7, r7), (8, .word pa2)] }) := by
  dsimp only
  obtain ⟨ck, r0, r1, r2, r5, r6, r7, hck, hrun⟩ :=
    evaluate_partial_data_bounded (q0 := q0) (q1 := q1) (q2 := q2) (q5 := q5)
      (q6 := q6) (q7 := q7) (q8 := q8) (q9 := q9)
      s hm hu hc hgs hrs hsl hws hw2 hlen hls hg hshift
  refine ⟨ck, r0, r1, r2, r5, r6, r7, hck, ?_⟩
  have hget : evaluate (.get 8 .otherHeap, { s with
      memory := m
      clock := s.clock + ck
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }) =
      (none, { dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s with
        clock := s.clock + ck }) := by
    simp [evaluate_get, dataInputState, setVar,
      StackSemRegisterTransfers.storeOfSyntax, hu, ho]
  rw [listSeqHOL, evaluate_seq_none _ _ _ _ hget
    (by change s.clock + ck ≤ s.clock + ck; exact Nat.le_refl _)]
  simpa only [listSeqHOL, dataInputState, setVar] using hrun


theorem evaluate_partial_data_tail_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {other curr gs rs i pa i2 pa2 b1 w endh trig : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 q9 : WordLocW width}
    {m m2 m3 : BitVec width → WordLocW width}
    (genSizes : List Nat) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i, pa, curr, m, s.mdomain, gs, rs) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (hr : s.store.lookup .nextFree = some ret)
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hcopy : memcpy ((pa2 - other) >>> wordShiftAmount width) other (curr + gs)
      m2 s.mdomain = (b1, m3, true))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, q9)] }
    ∃ ck regs,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width ∧
      evaluate (listSeqHOL ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3]),
        { R with clock := R.clock + ck }) =
        (none, { s with
          memory := m3
          regs := regs
          store := s.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kd, d0, d1, d2, d5, d6, d7, hkd, hd⟩ :=
    evaluate_partial_data_with_prefix_bounded (q0 := q0) (q1 := q1) (q2 := q2)
      (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8) (q9 := q9)
      s hm hu hc ho hgs hrs hsl hws hw2 hlen hls hg hshift
  let S := dataInputState other i pa q0 q1 q2 q5 q6 q7 q8 q9 m s
  let D := { S with
    memory := m2
    regs := S.regs.updateListEq [(0, d0), (1, d1), (2, d2), (3, .word pa2),
      (4, .word i2), (5, d5), (6, d6), (7, d7), (8, .word pa2)] }
  obtain ⟨copyReg, r7, r1, r4, htail⟩ := evaluate_partial_memcpy_tail genSizes
    pa2 other gs b1 w endh trig curr ret m3 D hg hu
    (by simp [D, HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, FUPDATE_HOL])
    ho hgsStore hr he ht hw hc hws hcopy
  let P := memcpySetupState pa2 other gs curr D
  let M := { P with
    memory := m3
    regs := P.regs.updateListEq [(0, .word 0), (1, copyReg),
      (2, .word (other + ((pa2 - other) >>> wordShiftAmount width) * wordSemBytesInWord)),
      (3, .word b1)] }
  let T0 := triggerSetupState b1 endh trig ret M
  let T := { T0 with
    regs := ((T0.regs.updateEq (1, r1)).updateEq (7, r7)).updateEq (4, r4)
    store := T0.store.updateEq (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)) }
  let final := cleanupState w endh b1 curr T
  have hstate : final = { s with
      memory := m3
      regs := final.regs
      store := s.store.updateListEq [(.nextFree, .word b1),
        (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
        (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] } := by
    rfl
  have hcopyBound : ((pa2 - other) >>> wordShiftAmount width).toNat ≤ 2 ^ width :=
    Nat.le_of_lt (BitVec.isLt _)
  refine ⟨kd + ((pa2 - other) >>> wordShiftAmount width).toNat, final.regs, ?_, ?_, ?_⟩
  · omega
  · rw [← hstate]
    apply evaluate_listSeq_collector_clocks _ _ (by simp) (by simp) _ D final
      kd ((pa2 - other) >>> wordShiftAmount width).toNat _
      (by simp [D, S, dataInputState, setVar]) hd htail
    intro x hx V
    simp only [List.dropLast_cons_cons, List.dropLast_singleton,
      List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst x
    exact evaluate_clock_of_leaf _ (Or.inl rfl) V
  · exact partial_final_return_register w b1 endh trig curr genSizes ret r7 r1 r4 M


theorem evaluate_partial_refs_tail_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {curr len endh gs rs i pa i2 pa2 other i3 pa3 b1 w trig : BitVec width}
    {q0 q1 q2 q5 q6 q7 q8 : WordLocW width}
    {m m2 m3 m4 : BitVec width → WordLocW width} {stack : List (WordLocW width)}
    (genSizes : List Nat) (ret : WordLocW width)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i, pa, curr, m, s.mdomain, true, gs, rs, curr + len) = (i2, pa2, m2, true))
    (hu : s.useStore = true) (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (hr : s.store.lookup .nextFree = some ret)
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hw : s.store.lookup .allocSize = some (.word w))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, rs) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hgs : s.store.lookup (.temp 0) = some (.word gs))
    (hrs : s.store.lookup (.temp 1) = some (.word rs))
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hls : conf.lenSize + 2 < width) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let R := { s with
      memory := m
      stack := stack
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa),
        (4, .word i), (5, q5), (6, q6), (7, q7), (8, q8), (9, .word 0)] }
    ∃ ck regs,
      ck ≤ 2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width) ∧
      evaluate (listSeqHOL ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3])),
        { R with clock := R.clock + ck }) =
        (none, { s with
          memory := m4
          stack := stack
          regs := regs
          store := s.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kr, r0, r1, r2, r5, r6, r7, r8, r9, hkr, href⟩ :=
    evaluate_partial_refs_with_prefix_bounded (q0 := q0) (q1 := q1) (q2 := q2)
      (q5 := q5) (q6 := q6) (q7 := q7) (q8 := q8) (stack := stack)
      s hm hu hc hl he hgs hrs hsl hws hw2 hlen hls hg hshift
  let S := refsInputState curr len endh i pa q0 q1 q2 q5 q6 q7 q8 m stack s
  let U := { S with
    memory := m2
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa2),
      (4, .word i2), (5, r5), (6, r6), (7, r7), (8, r8), (9, r9)] }
  obtain ⟨kt, regs, hkt, htail, hret⟩ :=
    evaluate_partial_data_tail_bounded (q0 := r0) (q1 := r1) (q2 := r2)
      (q5 := r5) (q6 := r6) (q7 := r7) (q8 := r8) (q9 := r9)
      genSizes ret S hmdata hu hc ho hgsStore hr he ht hw hmcopy hgs hrs
      hsl hws hw2 hlen hls hg hshift
  refine ⟨kr + kt, regs, ?_, ?_, hret⟩
  · omega
  apply evaluate_listSeq_collector_clocks _ _ (by simp) (by simp) _ U _ kr kt _
    (by simp [U, S, refsInputState, setVar]) href htail
  intro x hx V
  simp only [List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V


theorem evaluate_partial_roots_tail_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 i2 pa2 i3 pa3 b1 trig : BitVec width}
    {ret glob q0 q1 q2 q6 : WordLocW width}
    {m m1 m2 m3 m4 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)}
    (genSizes : List Nat)
    (s : StackSemStateFiniteExact width C F)
    (hm : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hu : s.useStore = true) (hus : s.useStack = true)
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hgsStore : s.store.lookup .genStart = some (.word gs))
    (ht : s.store.lookup .triggerGC = some (.word trig))
    (hmrefs : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i1, pa1, curr, m1, s.mdomain, true, gs, endh - curr, curr + len) =
      (i2, pa2, m2, true))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hls : conf.lenSize + 2 < width)
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hg : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    let B := setupState w gs endh curr len other ret glob s
    let M := { B with
      memory := m
      regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
        (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
    let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
    ∃ ck regs,
      ck ≤ (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width)) ∧
      evaluate (listSeqHOL ((partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]) ++
        ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3]))),
        { M with clock := M.clock + ck }) =
        (none, { s with
          memory := m4
          stack := s.stack.take s.stackSpace ++ stack1
          regs := regs
          store := S.store.updateListEq [(.nextFree, .word b1),
            (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
            (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  dsimp only
  obtain ⟨kr, r0, r1, r2, r5, r6, r7, r8, hkr, hroot⟩ :=
    evaluate_partial_roots_with_prefix_bounded (w := w) (len := len) (other := other)
      (moved := moved) (ret := ret) (glob := glob)
      (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      s hm hu hus hc hb hs hsl hws hw2 hlen hg hshift
  let S := rootsInputState conf w gs endh curr len other moved i pa ret glob q0 q1 q2 q6 m s
  let U := { S with
    memory := m1
    stack := s.stack.take s.stackSpace ++ stack1
    regs := S.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa1),
      (4, .word i1), (5, r5), (6, r6), (7, r7), (8, r8), (9, .word 0)] }
  obtain ⟨kt, regs, hkt, htail, hret⟩ :=
    evaluate_partial_refs_tail_bounded (w := w) (q0 := r0) (q1 := r1) (q2 := r2)
      (q5 := r5) (q6 := r6) (q7 := r7) (q8 := r8)
      (stack := s.stack.take s.stackSpace ++ stack1)
      genSizes ret S hmrefs hu
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hc)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using he)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ho)
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hgsStore)
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simpa [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using ht)
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]) hmdata hmcopy
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      (by simp [S, rootsInputState, rootsSetupState, setupState, setVar, setStore,
        HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])
      hsl hws hw2 hlen hls hg hshift
  refine ⟨kr + kt, regs, ?_, ?_, hret⟩
  · omega
  apply evaluate_listSeq_collector_clocks _ _ (by simp [partialRootsSetupCode])
    (by simp) _ U _ kr kt _
    (by simp [U, S, rootsInputState, rootsSetupState, setupState, setVar, setStore]) hroot htail
  intro x hx V
  simp only [partialRootsSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V


theorem evaluate_partial_program_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {w gs endh curr len other moved i pa i1 pa1 i2 pa2 i3 pa3 b1 trig : BitVec width}
    {ret glob : WordLocW width}
    {m m1 m2 m3 m4 : BitVec width → WordLocW width} {stack1 : List (WordLocW width)} (genSizes : List Nat) (s : StackSemStateFiniteExact width C F)
    (hu : s.useStore = true)
    (hr : s.regs.lookup 0 = some ret) (hw : s.regs.lookup 1 = some (.word w))
    (hgs : s.store.lookup .genStart = some (.word gs))
    (he : s.store.lookup .endOfHeap = some (.word endh))
    (hc : s.store.lookup .currHeap = some (.word curr))
    (hl : s.store.lookup .heapLength = some (.word len))
    (hg : s.store.lookup .globals = some glob)
    (ho : s.store.lookup .otherHeap = some (.word other))
    (hm : wordGenGcPartialMove conf (glob, gs >>> wordShiftAmount width,
      other, curr, s.memory, s.mdomain, gs, endh - curr) = (.word moved, i, pa, m, true))
    (hmroots : wordGenGcPartialMoveRootsBitmaps conf
      (s.stack.drop s.stackSpace, s.bitmaps, i, pa, curr, m, s.mdomain, gs, endh - curr) =
      (stack1, i1, pa1, m1, true))
    (hmrefs : wordGenGcPartialMoveRefList (2 ^ width) conf
      (endh, i1, pa1, curr, m1, s.mdomain, true, gs, endh - curr, curr + len) =
      (i2, pa2, m2, true))
    (hmdata : wordGenGcPartialMoveData conf (2 ^ width)
      (other, i2, pa2, curr, m2, s.mdomain, gs, endh - curr) = (i3, pa3, m3, true))
    (hmcopy : memcpy ((pa3 - other) >>> wordShiftAmount width) other (curr + gs)
      m3 s.mdomain = (b1, m4, true))
    (hus : s.useStack = true) (ht : s.store.lookup .triggerGC = some (.word trig))
    (hb : s.bitmaps.length < 2 ^ width - 1)
    (hs : s.stack.length * (width / 8) < 2 ^ width)
    (hls : conf.lenSize + 2 < width)
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0) (hgood : goodDimindex width)
    (hshift : ∀ x : BitVec width,
      x <<< wordShiftAmount width = x * wordSemBytesInWord) :
    ∃ ck regs,
      ck ≤ 2 ^ width + (s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width))) ∧
      evaluate (listSeqHOL ((partialSetupCode ++ [wordGenGcPartialMoveCode conf]) ++
        ((partialRootsSetupCode conf ++
        [wordGenGcPartialMoveRootsBitmapsCode conf]) ++
        ([.get 8 .currHeap, .get 9 .heapLength, addInst 9 8,
        .get 8 .endOfHeap, wordGenGcPartialMoveRefListCode conf] ++
        ([.get 8 .otherHeap, wordGenGcPartialMoveDataCode conf] ++
        [.get 2 .otherHeap, moveHOL 0 3, subInst 0 2,
          rightShiftInst 0 (wordShiftAmount width), .get 3 .genStart,
          .get 1 .currHeap, addInst 3 1, memcpyCode, .get 0 .nextFree,
          .set .nextFree 3, .get 8 .endOfHeap, .get 2 .triggerGC,
          setNewTrigger 8 3 genSizes, constInst 1 0, .set (.temp 0) 1,
          .set (.temp 1) 1, .get 1 .allocSize, subInst 8 3,
          .get 7 .currHeap, subInst 3 7, .set .genStart 3])))),
        { s with clock := s.clock + ck }) =
        (none, { s with
          memory := m4
          stack := s.stack.take s.stackSpace ++ stack1
          regs := regs
          store := (rootsSetupState conf moved curr
            (setupState w gs endh curr len other ret glob s)).store.updateListEq
            [(.nextFree, .word b1),
             (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
             (.temp 0, .word 0), (.temp 1, .word 0), (.genStart, .word (b1 - curr))] }) ∧
      regs.lookup 0 = some ret := by
  obtain ⟨km, q0, q1, q2, q6, hkm, hmove⟩ :=
    evaluate_partial_setup_move_bounded s hu hr hw hgs he hc hl hg ho hm hsl hws hw2 hlen hgood hshift
  let B := setupState w gs endh curr len other ret glob s
  let M := { B with
    memory := m
    regs := B.regs.updateListEq [(0, q0), (1, q1), (2, q2),
      (3, .word pa), (4, .word i), (5, .word moved), (6, q6)] }
  obtain ⟨kt, regs, hkt, htail, hret⟩ :=
    evaluate_partial_roots_tail_bounded (w := w) (q0 := q0) (q1 := q1) (q2 := q2) (q6 := q6)
      genSizes s hmroots hu hus hc hl he ho hgs ht hmrefs hmdata hmcopy hls hb hs
      hsl hws hw2 hlen hgood hshift
  have hrootsBound : (s.stack.drop s.stackSpace).length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) ≤ s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) :=
    Nat.mul_le_mul_right _ (by simp)
  refine ⟨km + kt, regs, ?_, ?_, hret⟩
  · omega
  apply evaluate_listSeq_collector_clocks _ _ (by simp [partialSetupCode])
    (by simp [partialRootsSetupCode]) s M _ km kt _
    (by simp [M, B, setupState, setVar, setStore]) hmove htail
  intro x hx V
  simp only [partialSetupCode, List.cons_append, List.nil_append,
    List.dropLast_cons_cons, List.dropLast_singleton,
    List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact evaluate_clock_of_leaf _ (Or.inl rfl) V
      | exact evaluate_clock_of_leaf _ (Or.inr ⟨_, rfl⟩) V


/-- Partial generational allocation correctness with a concrete clock allowance. -/
theorem alloc_correct_lemma_Generational_partial_bounded {width : Nat} [NeZero width] {C F : Type}
    {conf : Config} {genSizes : List Nat} {c : DataToWord.Config}
    {w : BitVec width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)} {l : HolFiniteMapExact Nat (WordLocW width)}
    {ret : WordLocW width} {anything : WordSemGcFun width}
    (ha : StackSemAllocation.alloc w s = (r, t)) (hr : r ≠ some .error)
    (hgc : s.gcFun = wordGcFun conf) (hk : conf.gcKind = .generational genSizes)
    (hbl : s.bitmaps.length < 2 ^ width - 1)
    (hstack : s.stack.length * (width / 8) < 2 ^ width)
    (hl0 : l.lookup 0 = some ret) (hl1 : l.lookup 1 = some (.word w))
    (hp : wordGenGcCanDoPartial genSizes (setStore .allocSize (.word w) s).store) :
    ∃ ck l2,
      ck ≤ 2 ^ width + (s.stack.length * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 2 ^ width))) ∧
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
  obtain ⟨hn, hcol⟩ := alloc_partial_collector ha hr hgc hk hp
  subst r
  let A := setStore .allocSize (.word w) s
  let curr := wordSemTheWord (holFapply A.store .currHeap)
  let other := wordSemTheWord (holFapply A.store .otherHeap)
  let gs := wordSemTheWord (holFapply A.store .genStart)
  let endh := wordSemTheWord (holFapply A.store .endOfHeap)
  let len := wordSemTheWord (holFapply A.store .heapLength)
  let trig := wordSemTheWord (holFapply A.store .triggerGC)
  let globalWord := wordSemTheWord (holFapply A.store .globals)
  obtain ⟨root, i0, pa0, m0, roots, i1, pa1, m1, i2, pa2, m2,
    i3, pa3, m3, b1, m4, hm, hmroots, hmrefs, hmdata, hmcopy,
    hass, hend, htrig, hfinal⟩ := partial_source_pipeline (s := A) hgc hk hp hcol
  obtain ⟨loads, hgood, hlen, hls, hsl⟩ := partial_source_loads conf A.store hass
  have hcurrA : A.store.lookup .currHeap = some (.word curr) := loads _ (by simp)
  have hotherA : A.store.lookup .otherHeap = some (.word other) := loads _ (by simp)
  have hgsA : A.store.lookup .genStart = some (.word gs) := loads _ (by simp)
  have hendA : A.store.lookup .endOfHeap = some (.word endh) := loads _ (by simp)
  have hlenA : A.store.lookup .heapLength = some (.word len) := loads _ (by simp)
  have htrigA : A.store.lookup .triggerGC = some (.word trig) := loads _ (by simp)
  have hglobA : A.store.lookup .globals = some (.word globalWord) := loads _ (by simp)
  have hc : s.store.lookup .currHeap = some (.word curr) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hcurrA
  have ho : s.store.lookup .otherHeap = some (.word other) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hotherA
  have hgs : s.store.lookup .genStart = some (.word gs) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hgsA
  have he : s.store.lookup .endOfHeap = some (.word endh) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hendA
  have hl : s.store.lookup .heapLength = some (.word len) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlenA
  have ht : s.store.lookup .triggerGC = some (.word trig) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using htrigA
  have hglob : s.store.lookup .globals = some (.word globalWord) := by
    simpa [A, setStore, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hglobA
  rw [holFapply_of_lookup hglobA] at hm
  have hrootword := partial_move_preserves_word conf globalWord
    (gs >>> wordShiftAmount width) other curr gs (endh - curr) s.memory s.mdomain
  change wordGenGcPartialMove conf (.word globalWord, gs >>> wordShiftAmount width,
    other, curr, s.memory, s.mdomain, gs, endh - curr) = (root, i0, pa0, m0, true) at hm
  rw [hm] at hrootword
  have hex : ∃ moved, root = .word moved := by
    cases root with
    | word moved => exact ⟨moved, rfl⟩
    | loc block offset => simp [wordSemIsWordLoc] at hrootword
  obtain ⟨moved, rfl⟩ := hex
  have hws : wordShiftAmount width < width := by
    unfold wordShiftAmount
    rcases hgood with h | h <;> simp [h]
  have hw2 : 2 < width := by
    rcases hgood with h | h <;> omega
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
  obtain ⟨ck, regs, hck, hrun, hret⟩ := evaluate_partial_program_bounded genSizes P rfl
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl0)
    (by simpa [P, R, setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hl1)
    hgs he hc hl hglob ho hm hmroots hmrefs hmdata hmcopy rfl ht hbl hstack
    hls hsl hws hw2 hlen hgood hshift
  rw [partial_final_store conf genSizes w gs endh curr len other moved b1
    ret (.word globalWord) P hc ho] at hrun
  have hamount : wordSemTheWord (holFapply A.store .allocSize) = w := by
    simp [A, setStore, holFapply, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, wordSemTheWord]
  rw [hamount] at hfinal
  have hstate : { P with
      memory := m4
      stack := s.stack.take s.stackSpace ++ roots
      regs := regs
      store := (P.store.updateEq (.allocSize, .word w)).updateListEq
        [(.currHeap, .word curr), (.otherHeap, .word other),
         (.nextFree, .word b1), (.genStart, .word (b1 - curr)),
         (.triggerGC, .word (b1 + newTrig (endh - b1) w genSizes)),
         (.globals, .word moved), (.globReal, globReal conf curr (.word moved)),
         (.temp 0, .word 0), (.temp 1, .word 0)] } =
      { t with
        useStore := true
        useStack := true
        useAlloc := false
        code := sptFromAList (compile c (sptToAList s.code))
        regs := regs
        gcFun := anything } := by
    rw [hfinal]
    rfl
  have hrunFinal := hrun.trans
    (congrArg (fun U => ((none : Option (StackSemResult width)), U)) hstate)
  refine ⟨ck, regs, ?_, ?_, by simp, ?_, fun _ => hret⟩
  · simpa [P, R, setVar] using hck
  · simp only [wordGcCode, hk]
    rw [evaluate_partial_select_from_source conf genSizes w _ _
      { R with clock := s.clock + ck } hass hp rfl hl1]
    rw [holFapply_of_lookup ht, holFapply_of_lookup he]
    simp only [wordSemTheWord]
    simpa only [partialProgramCode, partialSetupCode, partialRootsSetupCode,
      List.cons_append, List.nil_append, P, R, setVar] using hrunFinal
  · rw [hfinal]
    exact partial_empty_regs_submap regs



end SteppedFlapjack.StackAllocSteps
