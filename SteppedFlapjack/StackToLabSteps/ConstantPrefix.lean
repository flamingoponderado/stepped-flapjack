import SteppedFlapjack.LabToTargetSteps.EncodingStability
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

namespace SteppedFlapjack.Phase6

def P (x : BitVec 64) (t : HolProg 64) : HolProg 64 :=
  .seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) t))

/-- Stage 1: raw-call pass, generic tail and info. -/
theorem raw_P (info : Spt Nat) (x : BitVec 64) (t : HolProg 64) :
    StackRawCall.compTop info (P x t) =
      .seq (.stackAlloc 0) (.seq .skip (.seq (.inst (.const 1 x)) (StackRawCall.comp info t))) := by
  simp [P, StackRawCall.compTop, StackRawCall.comp, StackRawCall.compSeq, StackRawCall.destCase]

/-- Stage 2: allocation pass. -/
theorem alloc_P (n m : Nat) (x : BitVec 64) (t : HolProg 64) :
    StackAlloc.comp n m (P x t) =
      ((P x (StackAlloc.comp n m t).1), (StackAlloc.comp n m t).2) := by
  simp [P, StackAlloc.comp]

theorem nextLab_P (x y : BitVec 64) (t : HolProg 64) (k : Nat) :
    StackAlloc.nextLab (P x t) k = StackAlloc.nextLab (P y t) k := by
  simp [P, StackAlloc.nextLab]


def R (a : HolProg 64) (r : Nat) (x : BitVec 64) (t : HolProg 64) : HolProg 64 :=
  .seq a (.seq .skip (.seq (.inst (.const r x)) t))

theorem P_eq_R (x : BitVec 64) (t : HolProg 64) : P x t = R (.stackAlloc 0) 1 x t := rfl

/-- Stage 3: StackRemove. -/
theorem remove_R (jump : Bool) (bounds : BitVec 64 × BitVec 64) (ptr : Nat) (a : HolProg 64) (r : Nat)
    (x : BitVec 64) (t : HolProg 64) :
    StackRemove.comp jump bounds ptr (R a r x t) =
      R (StackRemove.comp jump bounds ptr a) r x (StackRemove.comp jump bounds ptr t) := by
  simp only [R]
  rw [StackRemove.comp, StackRemove.comp, StackRemove.comp]
  simp [StackRemove.comp]

/-- Stage 4: StackNames. -/
theorem names_R (names : Spt Nat) (a : HolProg 64) (r : Nat) (x : BitVec 64) (t : HolProg 64) :
    StackNames.progCompHOL names (R a r x t) =
      R (StackNames.progCompHOL names a) (StackNames.findNameSpt names r) x (StackNames.progCompHOL names t) := by
  simp [R, StackNames.progCompHOL, StackNames.instFindNameHOL]


open Flapjack.Compiler.Backend.StackToLab

theorem app_append {α : Type} (l r : AppList α) : appListAppend (.append l r) = appListAppend l ++ appListAppend r :=
  (appListAppend_thm l r []).1
theorem app_list {α : Type} (xs : List α) : appListAppend (.list xs) = xs := (appListAppend_thm .nil .nil xs).2.1

theorem nextLab_R (a : HolProg 64) (r : Nat) (x y : BitVec 64) (t : HolProg 64) (k : Nat) :
    StackAlloc.nextLab (R a r x t) k = StackAlloc.nextLab (R a r y t) k := by
  simp [R, StackAlloc.nextLab]

/-- Stage 5: the section for entry `id` has `x` in exactly one line. -/
theorem section_R (id : Nat) (a : HolProg 64) (r : Nat) (t : HolProg 64) :
    ∃ L1 L2 : List (LabSem.LabLineHOL 64), ∀ x : BitVec 64,
      progToSectionHOL (id, R a r x t) = ⟨id, L1 ++ .asm (.asmi (.inst (.const r x))) [] 0 :: L2⟩ := by
  let m := StackAlloc.nextLab (R a r 0 t) 2
  let fa := flattenHOL false a id m [] []
  let ft := flattenHOL false t id fa.2.2 [] []
  refine ⟨appListAppend fa.1 ++ [LabLang.Line.label id 1 0], appListAppend ft.1 ++ [LabLang.Line.label id ft.2.2 0], fun x => ?_⟩
  have hm : StackAlloc.nextLab (R a r x t) 2 = m := nextLab_R a r x 0 t 2
  simp only [progToSectionHOL]
  rw [hm]
  simp only [R, flattenHOL, isSeqHOL, if_true, Bool.false_eq_true, if_false]
  simp only [app_append, app_list, List.append_assoc, List.cons_append, List.nil_append, fa, ft, m]


theorem split4 {α : Type} (l : List α) (p q r s : α) : l ++ [p, q, r, s] = (l ++ [p, q, r]) ++ [s] := by simp

def prefixCode (x : BitVec 64) (a b c t : HolProg 64) : List (Nat × HolProg 64) :=
  [(5,a),(6,b),(64,c),(65,P x t)]

theorem info_prefix (x : BitVec 64) (a b c t : HolProg 64) :
    StackRawCall.collectInfo (prefixCode x a b c t) .ln = StackRawCall.collectInfo (prefixCode 0 a b c t) .ln := by
  simp [prefixCode, StackRawCall.collectInfo, StackRawCall.seqStackAlloc, P]

theorem nextLabHOL_P (x y : BitVec 64) (t : HolProg 64) (k : Nat) :
    StackAlloc.nextLabHOL (P x t) k = StackAlloc.nextLabHOL (P y t) k := nextLab_P x y t k

/-- Whole Stack→Lab compile of the countdown-shaped table: `x` occurs in exactly one line. -/
theorem compile_prefix (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec 64 × BitVec 64) (a b c t : HolProg 64) :
    ∃ (pre : List (LabLang.Section (LabSem.LabLineHOL 64))) (L1 L2 : List (LabSem.LabLineHOL 64)) (r : Nat),
      ∀ x : BitVec 64, StackToLab.compile sc dc mh sp off (prefixCode x a b c t) =
        pre ++ [⟨65, L1 ++ .asm (.asmi (.inst (.const r x))) [] 0 :: L2⟩] := by
  let info := StackRawCall.collectInfo (prefixCode 0 a b c t) .ln
  let t1 := StackRawCall.comp info t
  let m0 := StackAlloc.nextLabHOL (P 0 t1) 2
  let t2 := (StackAlloc.comp 65 m0 t1).1
  let rm := StackRemove.comp (width := 64) sc.jump off sp
  let nm := StackNames.progCompHOL (width := 64) sc.regNames
  obtain ⟨L1, L2, hsec⟩ := section_R 65 (nm (rm (.stackAlloc 0))) (StackNames.findNameSpt sc.regNames 1) (nm (rm t2))
  refine ⟨?pre, L1, L2, StackNames.findNameSpt sc.regNames 1, fun x => ?_⟩
  rotate_left
  have h65 : StackToLab.progToSectionHOL (65, nm (rm (StackAlloc.progComp (65, StackRawCall.compTop info (P x t))).2)) =
      ⟨65, L1 ++ .asm (.asmi (.inst (.const (StackNames.findNameSpt sc.regNames 1) x))) [] 0 :: L2⟩ := by
    rw [raw_P, StackAlloc.progComp]
    dsimp only
    rw [← P, nextLabHOL_P x 0, alloc_P]
    dsimp only [rm, nm]
    rw [P_eq_R, remove_R, names_R]
    exact hsec x
  simp only [StackToLab.compile, StackRawCall.compile, StackAlloc.compile, StackRemove.compileHOL,
    StackNames.compileHOL, info_prefix x]
  simp only [prefixCode, List.map_cons, List.map_nil, List.map_append]
  have h65' : StackToLab.progToSectionHOL (StackNames.progCompEntryHOL sc.regNames (StackRemove.progComp sc.jump off sp
      (StackAlloc.progComp (65, StackRawCall.compTop (StackRawCall.collectInfo [(5, a), (6, b), (64, c), (65, P 0 t)] .ln) (P x t))))) =
      ⟨65, L1 ++ .asm (.asmi (.inst (.const (StackNames.findNameSpt sc.regNames 1) x))) [] 0 :: L2⟩ := h65
  rw [h65', ← List.append_assoc, split4]

end SteppedFlapjack.Phase6

namespace SteppedFlapjack.Phase6
open Flapjack.Compiler.Backend.LabFilter

theorem filterSkip_last (pre : List (LabLang.Section (LabSem.LabLineHOL 64))) (id : Nat)
    (L1 L2 : List (LabSem.LabLineHOL 64)) (l : LabSem.LabLineHOL 64) (hl : notSkip l = true) :
    filterSkip (pre ++ [⟨id, L1 ++ l :: L2⟩]) =
      filterSkip pre ++ [⟨id, L1.filter notSkip ++ l :: L2.filter notSkip⟩] := by
  induction pre with
  | nil => simp [filterSkip, List.filter_append, hl]
  | cons s rest ih => obtain ⟨n, xs⟩ := s; simp [filterSkip, ih]

theorem forall₂_refl_list {α : Type} {Rel : α → α → Prop} (hr : ∀ a, Rel a a) (l : List α) : List.Forall₂ Rel l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (hr a) ih

theorem forall₂_mid {α : Type} {Rel : α → α → Prop} (hr : ∀ a, Rel a a) (L1 L2 : List α) {a b : α} (h : Rel a b) :
    List.Forall₂ Rel (L1 ++ a :: L2) (L1 ++ b :: L2) := by
  induction L1 with
  | nil => exact .cons h (forall₂_refl_list hr L2)
  | cons c L ih => exact .cons (hr c) ih

/-- End to end: label removal on the filtered Lab code of the countdown-shaped
Stack table is related for any two constants in the same encoding regime. -/
theorem prefix_removeLabels_rel (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec 64 × BitVec 64) (a b c t : HolProg 64)
    (clock pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (x y : BitVec 64) (h : constCount x = constCount y) :
    OptRel (removeLabels clock riscvConfig pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off (prefixCode x a b c t))))
      (removeLabels clock riscvConfig pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off (prefixCode y a b c t)))) := by
  obtain ⟨pre, L1, L2, r, hc⟩ := compile_prefix sc dc mh sp off a b c t
  rw [hc x, hc y, filterSkip_last _ _ _ _ _ rfl, filterSkip_last _ _ _ _ _ rfl]
  apply removeLabels_rel
  unfold PreCodeRel
  apply forall₂_mid (fun s => ⟨rfl, forall₂_refl_list (fun l => PreRel.refl l) _⟩) (filterSkip pre) []
  exact ⟨rfl, forall₂_mid (fun l => PreRel.refl l) _ _ (PreRel.asm _ _ _ _ _ _ (const_enc_length_eq r r x y h))⟩


end SteppedFlapjack.Phase6
