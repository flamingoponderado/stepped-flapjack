import Flapjack.Compiler.Backend.LabFilter
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabToTarget.ShmemInfo
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.RiscV.CorrectnessEncoding.Length
import Mathlib.Data.List.Forall2
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

namespace SteppedFlapjack.Phase6
variable {width : Nat} [NeZero width]

abbrev L (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)

/-- Lines agree except an instruction line's payload and bytes, at equal length. -/
inductive LineRel : L width → L width → Prop
  | refl (x : L width) : LineRel x x
  | asm (i i' : HolAsm width) (b b' : List (BitVec 8)) (l : Nat) (hb : b.length = b'.length) :
      LineRel (.asm (.asmi i) b l) (.asm (.asmi i') b' l)

def SecRel (s s' : Section (L width)) : Prop := s.sectionId = s'.sectionId ∧ List.Forall₂ LineRel s.lines s'.lines
def CodeRel (c c' : List (Section (L width))) : Prop := List.Forall₂ SecRel c c'

theorem sectionLabels_rel {xs xs' : List (L width)} (h : List.Forall₂ LineRel xs xs') :
    ∀ pos labs, sectionLabels pos xs labs = sectionLabels pos xs' labs := by
  induction h with
  | nil => intros; rfl
  | @cons x x' l1 l2 hx _ ih =>
    intro pos labs
    cases hx with
    | refl => cases x <;> simp only [sectionLabels] <;> (try split) <;> apply ih
    | asm => simp only [sectionLabels]; apply ih

theorem computeLabelsAlt_rel {c c' : List (Section (L width))} (h : CodeRel c c') :
    ∀ pos labs, computeLabelsAlt pos c labs = computeLabelsAlt pos c' labs := by
  induction h with
  | nil => intros; rfl
  | @cons s s' _ _ hs _ ih =>
    intro pos labs
    obtain ⟨hid, hl⟩ := hs
    simp only [computeLabelsAlt, sectionLabels_rel hl, hid]
    apply ih

theorem encLinesAgain_rel (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (enc : HolAsm width → List (BitVec 8))
    {xs xs' : List (L width)} (h : List.Forall₂ LineRel xs xs') :
    ∀ pos acc acc' ok, List.Forall₂ LineRel acc acc' →
      List.Forall₂ LineRel (encLinesAgain labs ffis pos enc xs acc ok).1 (encLinesAgain labs ffis pos enc xs' acc' ok).1 ∧
      (encLinesAgain labs ffis pos enc xs acc ok).2 = (encLinesAgain labs ffis pos enc xs' acc' ok).2 := by
  induction h with
  | nil =>
    intro pos acc acc' ok hacc
    exact ⟨by simpa only [encLinesAgain] using List.forall₂_reverse_iff.mpr hacc, by simp only [encLinesAgain]⟩
  | @cons x x' l1 l2 hx _ ih =>
    intro pos acc acc' ok hacc
    cases hx with
    | refl =>
      cases x with
      | label => exact ih _ _ _ _ (.cons (.refl _) hacc)
      | asm => exact ih _ _ _ _ (.cons (.refl _) hacc)
      | labAsm a w bytes l =>
        simp only [encLinesAgain]
        split
        · exact ih _ _ _ _ (.cons (.refl _) hacc)
        · exact ih _ _ _ _ (.cons (.refl _) hacc)
    | asm i i' b b' l hb => exact ih _ _ _ _ (.cons (.asm i i' b b' l hb) hacc)

theorem encSecsAgain_rel (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (enc : HolAsm width → List (BitVec 8))
    {c c' : List (Section (L width))} (h : CodeRel c c') :
    ∀ pos, CodeRel (encSecsAgain pos labs ffis enc c).1 (encSecsAgain pos labs ffis enc c').1 ∧
      (encSecsAgain pos labs ffis enc c).2 = (encSecsAgain pos labs ffis enc c').2 := by
  induction h with
  | nil => intro; exact ⟨.nil, rfl⟩
  | @cons s s' c1 c2 hs _ ih =>
    intro pos
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨hid, hl⟩ := hs
    dsimp only at hid hl
    subst hid
    have hr := encLinesAgain_rel labs ffis enc hl pos [] [] true .nil
    simp only [encSecsAgain]
    generalize encLinesAgain labs ffis pos enc lines [] true = A at hr
    generalize encLinesAgain labs ffis pos enc lines' [] true = B at hr
    obtain ⟨a1, p1, o1⟩ := A
    obtain ⟨b1, p2, o2⟩ := B
    obtain ⟨hr1, hr2⟩ := hr
    simp only [Prod.mk.injEq] at hr2
    obtain ⟨rfl, rfl⟩ := hr2
    obtain ⟨h3, h4⟩ := ih p1
    generalize encSecsAgain p1 labs ffis enc c1 = C at h3 h4
    generalize encSecsAgain p1 labs ffis enc c2 = D at h3 h4
    obtain ⟨c3, o3⟩ := C
    obtain ⟨d3, o4⟩ := D
    dsimp only at h3 h4 ⊢
    subst h4
    exact ⟨.cons ⟨rfl, hr1⟩ h3, rfl⟩

theorem linesUpdLabLen_rel {xs xs' : List (L width)} (h : List.Forall₂ LineRel xs xs') :
    ∀ pos acc acc', List.Forall₂ LineRel acc acc' →
      List.Forall₂ LineRel (linesUpdLabLen pos xs acc).1 (linesUpdLabLen pos xs' acc').1 ∧
      (linesUpdLabLen pos xs acc).2 = (linesUpdLabLen pos xs' acc').2 := by
  induction h with
  | nil =>
    intro pos acc acc' hacc
    exact ⟨by simpa only [linesUpdLabLen] using List.forall₂_reverse_iff.mpr hacc, by simp only [linesUpdLabLen]⟩
  | @cons x x' l1 l2 hx _ ih =>
    intro pos acc acc' hacc
    cases hx with
    | refl => cases x <;> exact ih _ _ _ (.cons (.refl _) hacc)
    | asm i i' b b' l hb => exact ih _ _ _ (.cons (.asm i i' b b' l hb) hacc)

theorem updLabLen_rel {c c' : List (Section (L width))} (h : CodeRel c c') :
    ∀ pos, CodeRel (updLabLen pos c) (updLabLen pos c') := by
  induction h with
  | nil => intro; exact .nil
  | @cons s s' c1 c2 hs _ ih =>
    intro pos
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨hid, hl⟩ := hs
    dsimp only at hid hl
    subst hid
    have hr := linesUpdLabLen_rel hl pos [] [] .nil
    simp only [updLabLen]
    generalize linesUpdLabLen pos lines [] = A at hr
    generalize linesUpdLabLen pos lines' [] = B at hr
    obtain ⟨a1, p1⟩ := A
    obtain ⟨b1, p2⟩ := B
    obtain ⟨hr1, hr2⟩ := hr
    dsimp only at hr1 hr2 ⊢
    subst hr2
    exact .cons ⟨rfl, hr1⟩ (ih _)

theorem padBytes_length (b b' : List (BitVec 8)) (l : Nat) (nop : List (BitVec 8)) (hb : b.length = b'.length) :
    (padBytes b l nop).length = (padBytes b' l nop).length := by
  unfold padBytes
  simp only [hb]
  split
  · exact hb
  · simp only [List.length_take, List.length_append, hb]

theorem addNop_rel (nop : List (BitVec 8)) {xs xs' : List (L width)} (h : List.Forall₂ LineRel xs xs') :
    List.Forall₂ LineRel (addNop nop xs) (addNop nop xs') := by
  induction h with
  | nil => exact .nil
  | @cons x x' l1 l2 hx hrest ih =>
    cases hx with
    | refl =>
      cases x with
      | label => exact .cons (.refl _) ih
      | asm => exact .cons (.refl _) hrest
      | labAsm => exact .cons (.refl _) hrest
    | asm i i' b b' l hb =>
      exact .cons (.asm i i' _ _ _ (by simp [hb])) hrest

theorem padSection_rel (nop : List (BitVec 8)) {xs xs' : List (L width)} (h : List.Forall₂ LineRel xs xs') :
    ∀ aux aux', List.Forall₂ LineRel aux aux' →
      List.Forall₂ LineRel (padSection nop xs aux) (padSection nop xs' aux') := by
  induction h with
  | nil => intro aux aux' ha; simpa only [padSection] using List.forall₂_reverse_iff.mpr ha
  | @cons x x' l1 l2 hx _ ih =>
    intro aux aux' ha
    cases hx with
    | refl =>
      cases x with
      | label l1 l2 len =>
        simp only [padSection]
        apply ih
        refine .cons (.refl _) ?_
        split
        · exact ha
        · exact addNop_rel nop ha
      | asm => exact ih _ _ (.cons (.refl _) ha)
      | labAsm => exact ih _ _ (.cons (.refl _) ha)
    | asm i i' b b' l hb =>
      exact ih _ _ (.cons (.asm i i' _ _ l (padBytes_length b b' l nop hb)) ha)

theorem padCode_rel (nop : List (BitVec 8)) {c c' : List (Section (L width))} (h : CodeRel c c') :
    CodeRel (padCode nop c) (padCode nop c') := by
  induction h with
  | nil => exact .nil
  | @cons s s' c1 c2 hs _ ih =>
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨hid, hl⟩ := hs
    dsimp only at hid hl
    subst hid
    exact .cons ⟨rfl, padSection_rel nop hl [] [] .nil⟩ ih

theorem allEncOkLight_rel (config : AsmConfigExact width) {c c' : List (Section (L width))} (h : CodeRel c c') :
    allEncOkLight config c = allEncOkLight config c' := by
  unfold allEncOkLight
  induction h with
  | nil => rfl
  | @cons s s' c1 c2 hs _ ih =>
    simp only [List.all_cons, ih]
    congr 1
    unfold secOkLight
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨-, hl⟩ := hs
    dsimp only at hl ⊢
    induction hl with
    | nil => rfl
    | @cons x x' l1 l2 hx _ ih2 =>
      simp only [List.all_cons, ih2]
      cases hx with
      | refl => rfl
      | asm => rfl

theorem getZeroLabsAcc_rel {c c' : List (Section (L width))} (h : CodeRel c c') :
    getZeroLabsAcc c = getZeroLabsAcc c' := by
  unfold getZeroLabsAcc
  induction h with
  | nil => rfl
  | @cons s s' c1 c2 hs _ ih =>
    simp only [List.foldr_cons, ih]
    unfold secGetZeroLabsAcc
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨-, hl⟩ := hs
    dsimp only at hl ⊢
    generalize List.foldr secGetZeroLabsAcc .ln c2 = acc
    induction hl with
    | nil => rfl
    | @cons x x' l1 l2 hx _ ih2 =>
      simp only [List.foldr_cons, ih2]
      cases hx with
      | refl => rfl
      | asm => rfl

inductive OptRel : Option (List (Section (L width)) × Spt (Spt Nat)) → Option (List (Section (L width)) × Spt (Spt Nat)) → Prop
  | none : OptRel none none
  | some (c c' labs) : CodeRel c c' → OptRel (some (c,labs)) (some (c',labs))

theorem finish_rel (config : AsmConfigExact width) (pos : Nat) (initLabs : Spt (Spt Nat)) (ffis : List HolFfiName)
    {b b' : List (Section (L width))} (h1 : CodeRel b b') :
    OptRel
      (let secList := updLabLen pos b
       let labs := computeLabelsAlt pos secList initLabs
       let (secList, done) := encSecsAgain pos labs ffis config.encode secList
       let secList := padCode (config.encode (.inst .skip)) secList
       if done && allEncOkLight config secList && zeroLabsAccExist labs secList then some (secList, labs) else none)
      (let secList := updLabLen pos b'
       let labs := computeLabelsAlt pos secList initLabs
       let (secList, done) := encSecsAgain pos labs ffis config.encode secList
       let secList := padCode (config.encode (.inst .skip)) secList
       if done && allEncOkLight config secList && zeroLabsAccExist labs secList then some (secList, labs) else none) := by
  have u := updLabLen_rel h1 pos
  dsimp only
  rw [computeLabelsAlt_rel u]
  have e := encSecsAgain_rel (computeLabelsAlt pos (updLabLen pos b') initLabs) ffis config.encode u pos
  generalize encSecsAgain pos (computeLabelsAlt pos (updLabLen pos b') initLabs) ffis config.encode (updLabLen pos b) = C at e
  generalize encSecsAgain pos (computeLabelsAlt pos (updLabLen pos b') initLabs) ffis config.encode (updLabLen pos b') = D at e
  obtain ⟨cc, dc⟩ := C
  obtain ⟨dd, ddn⟩ := D
  obtain ⟨h2, e2⟩ := e
  dsimp only at h2 e2 ⊢
  subst e2
  have p := padCode_rel (config.encode (.inst .skip)) h2
  rw [allEncOkLight_rel config p]
  unfold zeroLabsAccExist
  rw [getZeroLabsAcc_rel p]
  split
  · exact .some _ _ _ p
  · exact .none

/-- Label removal respects same-length instruction-payload substitution. -/
theorem removeLabelsLoop_rel (config : AsmConfigExact width) (pos : Nat) (initLabs : Spt (Spt Nat))
    (ffis : List HolFfiName) (clock : Nat) :
    ∀ {c c' : List (Section (L width))}, CodeRel c c' →
      OptRel (removeLabelsLoop clock config pos initLabs ffis c) (removeLabelsLoop clock config pos initLabs ffis c') := by
  induction clock with
  | zero =>
    intro c c' h
    rw [removeLabelsLoop, removeLabelsLoop]
    rw [computeLabelsAlt_rel h]
    have e := encSecsAgain_rel (computeLabelsAlt pos c' initLabs) ffis config.encode h pos
    generalize encSecsAgain pos (computeLabelsAlt pos c' initLabs) ffis config.encode c = A at e
    generalize encSecsAgain pos (computeLabelsAlt pos c' initLabs) ffis config.encode c' = B at e
    obtain ⟨a, da⟩ := A
    obtain ⟨b, db⟩ := B
    obtain ⟨h1, e1⟩ := e
    dsimp only at h1 e1 ⊢
    subst e1
    cases da
    · simp only [Bool.false_eq_true, if_false, if_true]; exact .none
    · simp only [if_true]; exact finish_rel config pos initLabs ffis h1
  | succ k ih =>
    intro c c' h
    rw [removeLabelsLoop, removeLabelsLoop]
    rw [computeLabelsAlt_rel h]
    have e := encSecsAgain_rel (computeLabelsAlt pos c' initLabs) ffis config.encode h pos
    generalize encSecsAgain pos (computeLabelsAlt pos c' initLabs) ffis config.encode c = A at e
    generalize encSecsAgain pos (computeLabelsAlt pos c' initLabs) ffis config.encode c' = B at e
    obtain ⟨a, da⟩ := A
    obtain ⟨b, db⟩ := B
    obtain ⟨h1, e1⟩ := e
    dsimp only at h1 e1 ⊢
    subst e1
    cases da
    · simp only [Bool.false_eq_true, if_false, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      exact ih h1
    · simp only [if_true]; exact finish_rel config pos initLabs ffis h1

/-- Before encoding: instruction lines whose encodings have equal length. -/
inductive PreRel (enc : HolAsm width → List (BitVec 8)) : L width → L width → Prop
  | refl (x : L width) : PreRel enc x x
  | asm (i i' : HolAsm width) (b b' : List (BitVec 8)) (l l' : Nat) (h : (enc i).length = (enc i').length) :
      PreRel enc (.asm (.asmi i) b l) (.asm (.asmi i') b' l')

def PreCodeRel (enc : HolAsm width → List (BitVec 8)) (c c' : List (Section (L width))) : Prop :=
  List.Forall₂ (fun s s' => s.sectionId = s'.sectionId ∧ List.Forall₂ (PreRel enc) s.lines s'.lines) c c'

theorem encSecList_rel (enc : HolAsm width → List (BitVec 8)) {c c' : List (Section (L width))}
    (h : PreCodeRel enc c c') : CodeRel (encSecList enc c) (encSecList enc c') := by
  unfold encSecList
  induction h with
  | nil => exact .nil
  | @cons s s' c1 c2 hs _ ih =>
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    refine .cons ⟨hs.1, ?_⟩ ih
    obtain ⟨-, hl⟩ := hs
    simp only [encSec]
    dsimp only at hl ⊢
    induction hl with
    | nil => exact .nil
    | @cons x x' l1 l2 hx _ ih2 =>
      refine .cons ?_ ih2
      cases hx with
      | refl => exact .refl _
      | asm i i' b b' l l' hlen =>
        simp only [encLine, cbwToAsmExact, cbwToAsmHOL]
        have r := LineRel.asm (width := width) i i' (enc i) (enc i') (enc i).length hlen
        rw [hlen] at r ⊢
        exact r

theorem removeLabels_rel (clock : Nat) (config : AsmConfigExact width) (pos : Nat) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) {c c' : List (Section (L width))} (h : PreCodeRel config.encode c c') :
    OptRel (removeLabels clock config pos labs ffis c) (removeLabels clock config pos labs ffis c') :=
  removeLabelsLoop_rel config pos labs ffis clock (encSecList_rel config.encode h)

theorem progToBytes_length_rel {c c' : List (Section (L width))} (h : CodeRel c c') :
    (progToBytes c).length = (progToBytes c').length := by
  rw [progToBytesMap, progToBytesMap]
  induction h with
  | nil => rfl
  | @cons s s' c1 c2 hs _ ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, ih]
    congr 1
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨-, hl⟩ := hs
    dsimp only at hl ⊢
    induction hl with
    | nil => rfl
    | @cons x x' l1 l2 hx _ ih2 =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, ih2]
      cases hx with
      | refl => rfl
      | asm _ _ _ _ _ hb => simp only [lineBytes, hb]

end SteppedFlapjack.Phase6

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.L3

namespace SteppedFlapjack.Phase6

/-- Number of RISC-V instructions `riscvAst` emits for a 64-bit constant. -/
def constCount (i : BitVec 64) : Nat :=
  if i == (holWordExtract 12 11 0 i).signExtend 64 then 1
  else if (holWordExtract 32 63 32 i == 0 && !i.getLsbD 31) ||
          (holWordExtract 32 63 32 i == -1 && i.getLsbD 31) then 2
  else 6

theorem riscvAst_const_length (r : Nat) (i : BitVec 64) :
    (riscvAst (.inst (.const r i))).length = constCount i := by
  simp only [riscvAst, constCount]
  split
  · rfl
  · split
    · simp only [riscvConst32]; split <;> rfl
    · split <;> simp only [riscvConst32, List.length_append] <;> split <;> split <;> rfl

/-- Same constant regime ⇒ same encoded length (any registers). -/
theorem const_enc_length_eq (r r' : Nat) (i i' : BitVec 64) (h : constCount i = constCount i') :
    (riscvConfig.encode (.inst (.const r i))).length = (riscvConfig.encode (.inst (.const r' i'))).length := by
  rw [riscvConfig_encode, Flapjack.RiscV.TargetProof.riscvEnc_length_eq,
    Flapjack.RiscV.TargetProof.riscvEnc_length_eq, riscvAst_const_length, riscvAst_const_length, h]

/-- Every constant falls in one of three regimes, so three representatives cover all n. -/
theorem constCount_cases (i : BitVec 64) :
    constCount i = constCount 0 ∨ constCount i = constCount 2048 ∨ constCount i = constCount (BitVec.ofNat 64 (2^31)) := by
  have h0 : constCount 0 = 1 := by decide +kernel
  have h1 : constCount 2048 = 2 := by decide +kernel
  have h2 : constCount (BitVec.ofNat 64 (2^31)) = 6 := by decide +kernel
  rw [h0, h1, h2]
  unfold constCount
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

end SteppedFlapjack.Phase6

namespace SteppedFlapjack.Phase6
theorem getShmemInfo_rel {c c' : List (Section (L 64))} (h : CodeRel c c') :
    ∀ pos names info, getShmemInfo c pos names info = getShmemInfo c' pos names info := by
  induction h with
  | nil => intros; rfl
  | @cons s s' c1 c2 hs _ ih =>
    obtain ⟨ids, lines⟩ := s
    obtain ⟨ids', lines'⟩ := s'
    obtain ⟨hid, hl⟩ := hs
    dsimp only at hid hl
    subst hid
    induction hl with
    | nil => intros; simp only [getShmemInfo]; apply ih
    | @cons x x' l1 l2 hx _ ih2 =>
      intro pos names info
      cases hx with
      | refl =>
        rcases x with _ | ⟨ins, bs, len⟩ | _
        · simp only [getShmemInfo]; apply ih2
        · rcases ins with _ | _ | ⟨m, r, ⟨base, off⟩⟩
          · simp only [getShmemInfo]; apply ih2
          · simp only [getShmemInfo]; apply ih2
          · simp only [getShmemInfo]; apply ih2
        · simp only [getShmemInfo]; apply ih2
      | asm i i' b b' l hb => simp only [getShmemInfo, hb]; apply ih2

end SteppedFlapjack.Phase6
