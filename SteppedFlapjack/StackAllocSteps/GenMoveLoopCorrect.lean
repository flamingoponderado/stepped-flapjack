import SteppedFlapjack.StackAllocSteps.GenMoveDataCorrect
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CodeThm.GenGcMoveLoop

/-! Bounded-clock correctness for the full generational collector loop. -/

namespace SteppedFlapjack.StackAllocSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend
set_option maxHeartbeats 2000000

/-- Original loop output with an explicit extra-clock limit. -/
abbrev GenLoopOutputBounded {width : Nat} [NeZero width] {C F : Type}
    (budget : Nat) (conf : Config) (s : StackSemStateFiniteExact width C F)
    (i pa ib pb : BitVec width) (m : BitVec width → WordLocW width) : Prop :=
  ∃ ck r0 r1 r2 r5 r6 r7 r8 t0 t1 t4 t5 t6, ck ≤ budget ∧
    evaluate (wordGenGcMoveLoopCode conf, { s with clock := s.clock + ck }) =
      (none, { s with
        memory := m
        store := s.store.updateListEq [(.temp 0, t0), (.temp 1, t1), (.temp 2, .word pb),
          (.temp 3, .word ib), (.temp 4, t4), (.temp 5, t5), (.temp 6, t6)]
        regs := s.regs.updateListEq [(0, r0), (1, r1), (2, r2), (3, .word pa),
          (4, .word i), (5, r5), (6, r6), (7, r7), (8, r8)] })


/-- The data branch preserves the outer loop clock budget. -/
theorem genLoopDataBounded_case {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (k : Nat) (s : StackSemStateFiniteExact width C F)
    (pax i pa ib pb old tt i1 pa1 ib1 pb1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (hpa : pax ≠ pa)
    (r : GenLoopReady s pax i pa ib pb pb old tt)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pb, old, s.memory, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (ih : ∀ (s' : StackSemStateFiniteExact width C F) (pax' i' pa' ib' pb' pbx' tt' : BitVec width),
      wordGenGcMoveLoop conf (k - 1) (pax', i', pa', ib', pb', pbx', old, s'.memory, s'.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s' pax' i' pa' ib' pb' pbx' old tt' →
      GenLoopOutputBounded ((k - 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) conf s' i1 pa1 ib1 pb1 m1) :
    GenLoopOutputBounded (k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) conf s i1 pa1 ib1 pb1 m1 := by
  obtain ⟨i', pa', ib', pb', m', hk, hd, hr⟩ :=
    genLoopSource_data conf k pax i pa ib pb old s.memory s.mdomain i1 pa1 ib1 pb1 m1 hpa h
  obtain ⟨ckD, q0, q1, q2, q5, q6, q7, u0, u1, hDbound, hD⟩ :=
    genGcMoveDataBoundedClock hsl hws hw2 hlen hshift old (2 ^ width)
      pax i pa ib pb i' pa' ib' pb' m' s hd r.curr r.use r.temp0 r.temp1 r.temp2 r.temp3
      r.reg0 (by simp [r.reg1]) (by simp [r.reg2]) r.reg3 r.reg4 r.reg5 r.reg6
      (by simp [r.reg7]) r.reg8
  let d := genLoopDataNext s pb pb' i' pa' ib' m' q0 q1 q2 q5 q6 q7 u0 u1
  let t : StackSemStateFiniteExact width C F :=
    { s with
      memory := m'
      store := s.store.updateListEq [(.temp 0, u0), (.temp 1, u1), (.temp 2, .word pb'),
        (.temp 3, .word ib')]
      regs := s.regs.updateListEq [(0, q0), (1, q1), (2, q2), (3, .word pa'),
        (4, .word i'), (5, q5), (6, q6), (7, q7), (8, .word pa')] }
  have hb : evaluate (genLoopBody conf, { s with clock := s.clock + ckD }) = (none, d) := by
    exact genLoopBodyData_eval conf _ t pb pb' r.reg1 r.reg2 hD
      (by dsimp [t]; omega) r.use
      (by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL])
      (by simpa [t, FUPDATE_LIST_HOL, FUPDATE_HOL] using r.temp4)
  have rd := genLoopDataNext_ready s pax i pa ib pb old tt r
    pb' i' pa' ib' m' q0 q1 q2 q5 q6 q7 u0 u1
  obtain ⟨ckR, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hRbound, hR⟩ :=
    ih d pa' i' pa' ib' pb' pb (pb - pb') hr rd
  have htt : tt ≠ 0 := by
    intro ht
    exact hpa ((r.stop.mp ht).2)
  have hsum : (k - 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) = k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by
    calc
      _ = (k - 1 + 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by simp [Nat.add_mul]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbudget : ckD + ckR + 1 ≤ k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by omega
  refine ⟨ckD + ckR + 1, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hbudget, ?_⟩
  have H := genLoopStep_eval conf s d _ tt ckD ckR r.reg7 htt hb rfl hR
  refine H.trans ?_
  simp only [d, setVar, Prod.mk.injEq, true_and]
  rw [genLoopTemps_overwrite]
  congr 1
  apply regs_ext
  intro n
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL, HolFiniteMapExact.lookup_updateEq]
  by_cases n0 : n = 0
  · subst n0; simp
  by_cases n1 : n = 1
  · subst n1; simp
  by_cases n2 : n = 2
  · subst n2; simp
  by_cases n3 : n = 3
  · subst n3; simp
  by_cases n4 : n = 4
  · subst n4; simp
  by_cases n5 : n = 5
  · subst n5; simp
  by_cases n6 : n = 6
  · subst n6; simp
  by_cases n7 : n = 7
  · subst n7; simp
  by_cases n8 : n = 8
  · subst n8; simp
  simp [n0, n1, n2, n3, n4, n5, n6, n7, n8]


/-- The reference branch preserves the outer loop clock budget. -/
theorem genLoopRefsBounded_case {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (k : Nat) (s : StackSemStateFiniteExact width C F)
    (pax i pa ib pb pbx old tt i1 pa1 ib1 pb1 : BitVec width)
    (m1 : BitVec width → WordLocW width) (hpb : pbx ≠ pb)
    (r : GenLoopReady s pax i pa ib pb pbx old tt)
    (h : wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, s.memory, s.mdomain) =
      (i1, pa1, ib1, pb1, m1, true))
    (ih : ∀ (s' : StackSemStateFiniteExact width C F) (pax' i' pa' ib' pb' pbx' tt' : BitVec width),
      wordGenGcMoveLoop conf (k - 1) (pax', i', pa', ib', pb', pbx', old, s'.memory, s'.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s' pax' i' pa' ib' pb' pbx' old tt' →
      GenLoopOutputBounded ((k - 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) conf s' i1 pa1 ib1 pb1 m1) :
    GenLoopOutputBounded (k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) conf s i1 pa1 ib1 pb1 m1 := by
  obtain ⟨ha, i', pa', ib', pb', m', hk, hd, hr⟩ :=
    genLoopSource_refs conf k pax i pa ib pb pbx old s.memory s.mdomain i1 pa1 ib1 pb1 m1 hpb h
  let e := genLoopRefsEntry s pbx pb pax
  obtain ⟨ckD, q1, q2, q5, q6, q7, u0, u1, hDbound, hD⟩ :=
    genGcMoveRefsBoundedClock hsl hws hw2 hlen hshift pbx old (2 ^ width)
      pb i pa ib pb ha i' pa' ib' pb' m' e hd
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.curr)
      r.use
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp0)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp1)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp2)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp3)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.temp4)
      (by simp [e, setVar, setStore, FUPDATE_HOL])
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg1])
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg2])
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg3)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg4)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg5)
      (by simpa [e, genLoopRefsEntry, setVar, setStore, FUPDATE_HOL] using r.reg6)
      (by simp [e, setVar, setStore, FUPDATE_HOL, r.reg7])
      (by simp [e, setVar, setStore, FUPDATE_HOL])
  let t := genLoopRefsResult s pbx pb pax ha pb' i' pa' ib' m' q1 q2 q5 q6 q7 u0 u1
  let d := genLoopRefsNext s pbx pb pax pb' i' pa' ib' m' q6 u0 u1
  have ht5 : t.store.lookup (.temp 5) = some (.word pb) := by
    simp [t, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht6 : t.store.lookup (.temp 6) = some (.word pax) := by
    simp [t, genLoopRefsEntry, setVar, setStore, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht2 : t.store.lookup (.temp 2) = some (.word pb') := by
    simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht3 : t.regs.lookup 3 = some (.word pa') := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht4 : t.regs.lookup 4 = some (.word i') := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have ht8 : t.regs.lookup 8 = some (.word ha) := by simp [t, FUPDATE_LIST_HOL, FUPDATE_HOL]
  have hb : evaluate (genLoopBody conf, { s with clock := s.clock + ckD }) = (none, d) := by
    have H := genLoopBodyRefs_eval conf { s with clock := s.clock + ckD } t
      pbx pb pax ha pb' pa' i' hpb r.use r.reg1 r.reg2 r.reg8 hD
      (by dsimp [t, genLoopRefsEntry, setVar, setStore]; omega)
      r.use ht5 ht6 ht2 ht3 ht4 ht8
    have ht := genLoopRefsTail_eval t ha pb pb' pax pa' i' r.use ht5 ht6 ht2 ht3 ht4 ht8
    exact H.trans (ht.symm.trans (genLoopRefsTail_normalize s pbx pb pax ha pb' i' pa' ib'
      m' q1 q2 q5 q6 q7 u0 u1 r.use))
  have rd := genLoopRefsNext_ready s pax i pa ib pb pbx old tt r
    pb' i' pa' ib' m' q6 u0 u1
  obtain ⟨ckR, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hRbound, hR⟩ :=
    ih d pax i' pa' ib' pb' pb ((pb - pb') ||| (pax - pa')) hr rd
  have htt : tt ≠ 0 := by
    intro ht
    exact hpb ((r.stop.mp ht).1)
  have hsum : (k - 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) + (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) = k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by
    calc
      _ = (k - 1 + 1) * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by simp [Nat.add_mul]
      _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hbudget : ckD + ckR + 1 ≤ k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1) := by omega
  refine ⟨ckD + ckR + 1, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, hbudget, ?_⟩
  have H := genLoopStep_eval conf s d _ tt ckD ckR r.reg7 htt hb rfl hR
  refine H.trans ?_
  simp only [d, genLoopRefsEntry, setVar, setStore, Prod.mk.injEq, true_and]
  rw [genLoopRefsStore_overwrite]
  congr 1
  apply regs_ext
  intro n
  simp only [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL, List.foldl,
    FUPDATE_HOL]
  by_cases n0 : n = 0
  · subst n0; simp
  by_cases n1 : n = 1
  · subst n1; simp
  by_cases n2 : n = 2
  · subst n2; simp
  by_cases n3 : n = 3
  · subst n3; simp
  by_cases n4 : n = 4
  · subst n4; simp
  by_cases n5 : n = 5
  · subst n5; simp
  by_cases n6 : n = 6
  · subst n6; simp
  by_cases n7 : n = 7
  · subst n7; simp
  by_cases n8 : n = 8
  · subst n8; simp
  simp [n0, n1, n2, n3, n4, n5, n6, n7, n8]


/-- Full generational collection has a fuel-based extra-clock bound. -/
theorem genGcMoveLoopBoundedClock {width : Nat} [NeZero width] {C F : Type} {conf : Config}
    (hsl : shiftLength conf < width) (hws : wordShiftAmount width < width)
    (hw2 : 2 < width) (hlen : conf.lenSize ≠ 0)
    (hshift : ∀ w : BitVec width, w <<< wordShiftAmount width = w * wordSemBytesInWord)
    (old : BitVec width) :
    ∀ (k : Nat) (s : StackSemStateFiniteExact width C F)
      (pax i pa ib pb pbx tt i1 pa1 ib1 pb1 : BitVec width)
      (m1 : BitVec width → WordLocW width),
      wordGenGcMoveLoop conf k (pax, i, pa, ib, pb, pbx, old, s.memory, s.mdomain) =
        (i1, pa1, ib1, pb1, m1, true) →
      GenLoopReady s pax i pa ib pb pbx old tt → GenLoopOutputBounded (k * (2 ^ width * (2 ^ width * (2 ^ width + 1) + 1) + 1)) conf s i1 pa1 ib1 pb1 m1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s pax i pa ib pb pbx tt i1 pa1 ib1 pb1 m1 h r
    by_cases hpb : pbx = pb
    · subst pbx
      by_cases hpa : pax = pa
      · subst pax
        rw [wordGenGcMoveLoop] at h
        simp only [if_true, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := h
        have ht : tt = 0 := r.stop.mpr ⟨rfl, rfl⟩
        subst tt
        obtain ⟨r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, he⟩ :=
          genLoopStop_output conf s i pa ib pb pb pa r.temp0 r.temp1 r.temp5 r.temp6
            r.temp2 r.temp3 r.temp4 r.reg0 r.reg1 r.reg2 r.reg3 r.reg4 r.reg5 r.reg6
            r.reg7 r.reg8
        exact ⟨0, r0, r1, r2, r5, r6, r7, r8, t0, t1, t4, t5, t6, Nat.zero_le _, by simpa using he⟩
      · obtain ⟨_, _, _, _, _, hk, _, _⟩ :=
          genLoopSource_data conf k pax i pa ib pb old s.memory s.mdomain
            i1 pa1 ib1 pb1 m1 hpa h
        apply genLoopDataBounded_case hsl hws hw2 hlen hshift k s pax i pa ib pb old tt
          i1 pa1 ib1 pb1 m1 hpa r h
        intro s' pax' i' pa' ib' pb' pbx' tt' h' r'
        exact ih (k - 1) (by omega) s' pax' i' pa' ib' pb' pbx' tt'
          i1 pa1 ib1 pb1 m1 h' r'
    · obtain ⟨_, _, _, _, _, _, hk, _, _⟩ :=
        genLoopSource_refs conf k pax i pa ib pb pbx old s.memory s.mdomain
          i1 pa1 ib1 pb1 m1 hpb h
      apply genLoopRefsBounded_case hsl hws hw2 hlen hshift k s pax i pa ib pb pbx old tt
        i1 pa1 ib1 pb1 m1 hpb r h
      intro s' pax' i' pa' ib' pb' pbx' tt' h' r'
      exact ih (k - 1) (by omega) s' pax' i' pa' ib' pb' pbx' tt'
        i1 pa1 ib1 pb1 m1 h' r'


end SteppedFlapjack.StackAllocSteps
