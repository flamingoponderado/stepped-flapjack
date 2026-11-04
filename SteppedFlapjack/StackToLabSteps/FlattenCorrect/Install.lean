import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Call
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
import SteppedFlapjack.StackToLabSteps.FlattenCorrect.Guarded

/-! Adapted copy of
`Flapjack/Compiler/Backend/StackToLab/Proofs/FlattenCorrect/Install.lean`
(stepped-flapjack#2, phase C1): the `Install` case for `FlattenPropWithin`. The
flattened code runs two LabSem instructions, the `LocValue` of the return label
and `Install`. Otherwise the statements and proofs follow the original. -/

/-! `flatten_correct` case `Install` (`stack_to_labProofScript.sml:2398-2519`):
installing the oracle's next programs extends the LabSem code with their
sections, preserving `state_rel` (in particular the installation of every
procedure, old and new). -/

namespace SteppedFlapjack.StackToLabSteps
open Flapjack hiding flattenHOL
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
  (FlattenHyps FlattenConcl MeasureLt appListAppendList appListAppendAppend)
open SteppedFlapjack.StackSteps

section
variable {width : Nat} [NeZero width] {C F : Type}

theorem sptAListLookup_eq_holAlookup {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = holAlookup entries key
  | [] => rfl
  | (k, v) :: rest => by
    simp only [sptAListLookup, holAlookup]
    by_cases h : key = k
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
      exact sptAListLookup_eq_holAlookup key rest

theorem secLabelOkOfLabels {n : Nat} :
    ∀ (L : List (LabLineHOL width)),
      (∀ p ∈ Compiler.Backend.LabProps.LabelSets.extractLabels L, p.1 = n ∧ p.2 ≠ 0) →
      ∀ line ∈ L, Compiler.Backend.LabProps.secLabelOk n line := by
  intro L h line hl
  cases line with
  | label a b c =>
    have := h (a, b) (label_mem_extractLabels a b c L hl)
    exact ⟨this.1, this.2⟩
  | _ => trivial

theorem holAlookupIsSome_iff {α : Type} (entries : List (Nat × α)) (key : Nat) :
    (holAlookup entries key).isSome ↔ key ∈ entries.map Prod.fst := by
  induction entries with
  | nil => simp [holAlookup]
  | cons e rest ih =>
    obtain ⟨k, v⟩ := e
    by_cases h : k = key
    · subst h; simp [holAlookup]
    · simp only [holAlookup, h, if_false, ih, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm h
        · exact e

/-- The code part of `state_rel` after installing the oracle's next programs:
old procedures stay installed, new ones are installed in the appended
sections, the domains agree and every section's labels stay well formed. -/
theorem installCode {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    {progs : List (Nat × HolProg width)} (hprogs : (s.compileOracle 0).2.1 = progs) :
    (∀ k prog, sptLookup k (sptUnion s.code (sptFromAList progs)) = some prog →
      Compiler.Backend.StackProps.callArgs prog t.ptrReg t.lenReg t.ptr2Reg t.len2Reg t.linkReg ∧
      ∃ pc, codeInstalled pc (appListAppend (flattenHOL true prog k
          (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []).1) (t.code ++ progs.map
              progToSectionHOL) ∧
        locToPc k 0 (t.code ++ progs.map progToSectionHOL) = some pc) ∧
    (∀ x, sptDomain (sptUnion s.code (sptFromAList progs)) x ↔
      x ∈ (t.code ++ progs.map progToSectionHOL).map (·.sectionId)) ∧
    (∀ sec ∈ t.code ++ progs.map progToSectionHOL, Compiler.Backend.LabProps.secLabelsOk sec) := by
  obtain ⟨-, -, -, -, -, -, -, -, hcode, hdom, hsec, -, -, -, -, -, -, -, -, -, -, -, -, -,
    horc, -⟩ := rel
  obtain ⟨hk1, hk2⟩ := horc 0
  rw [hprogs] at hk1 hk2
  have lok : labelsOk (progs.map progToSectionHOL) :=
    progToSectionLabelsOk ⟨fun np h => ⟨fun p hp => (hk1 np h).2.1 p hp, (hk1 np h).2.2⟩, hk2⟩
  obtain ⟨secNew, -, -⟩ := labelsOkImp _ lok
  have lookNew : ∀ k, sptLookup k (sptFromAList progs) = holAlookup progs k := fun k => by
    rw [sptLookup_sptFromAList, sptAListLookup_eq_holAlookup]
  refine ⟨?_, ?_, ?_⟩
  · intro k prog h
    rw [sptLookup_sptUnion] at h
    split at h
    · rename_i v hv
      cases h
      obtain ⟨ca, pc, inst, entry⟩ := hcode k prog hv
      exact ⟨ca, pc, codeInstalledAppend _ _ _ _ inst, locToPcAppend _ _ _ _ _ entry⟩
    · rename_i hnone
      rw [lookNew] at h
      have mem := holAlookup_mem _ _ _ h
      have ca := (hk1 (k, prog) mem).1
      obtain ⟨pc, instN, entryN⟩ := codeInstalledProgToSection progs k prog ⟨lok, h⟩
      have notMem : k ∉ t.code.map (·.sectionId) := by
        intro hm
        have := (hdom k).mpr hm
        simp [sptDomain, hnone] at this
      have labOk : ∀ line ∈ appListAppend (flattenHOL true prog k
          (Compiler.Backend.StackAlloc.nextLabHOL prog 2) [] []).1,
              Compiler.Backend.LabProps.secLabelOk k line := by
        apply secLabelOkOfLabels
        intro p hp
        have hsecMem : progToSectionHOL (k, prog) ∈ progs.map progToSectionHOL :=
          List.mem_map_of_mem mem
        have := lok.2 _ hsecMem
        rw [progToSection_eq] at this
        apply this.1 p
        rw [Compiler.Backend.LabProps.LabelSets.extractLabels_append]
        exact List.mem_append_left _ hp
      refine ⟨ca, codeLength t.code + pc,
        codeInstalledAppend2 _ _ _ _ k ⟨notMem, hsec, labOk, instN⟩, ?_⟩
      rw [locToPcAppend2 k 0 _ _ pc ⟨notMem, hsec, entryN⟩, Nat.add_comm]
  · intro x
    rw [sptDomain_sptUnion]
    simp only [List.map_append, List.mem_append, mapProgToSectionFst]
    rw [← hdom x]
    simp only [sptDomain, lookNew, holAlookupIsSome_iff]
  · intro sec hs
    rcases List.mem_append.mp hs with h | h
    · exact hsec sec h
    · exact secNew sec h

/-- The state relation after an installation. -/
theorem stateRelInstall {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    {progs : List (Nat × HolProg width)} (hprogs : (s.compileOracle 0).2.1 = progs)
    (bm : List (BitVec width)) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width)
    (k n l P : Nat) :
    stateRel
      { s with
        bitmaps := s.bitmaps ++ bm
        codeBuffer := cb
        dataBuffer := db
        code := sptUnion s.code (sptFromAList progs)
        regs := (StackSemStateOps.restrictIn s.regs s.ffiSaveRegs).updateEq
          (t.ptrReg, .loc k 0)
        fpRegs := HolFiniteMapExact.empty
        compileOracle := holShiftSeq 1 s.compileOracle }
      { t with
        pc := P
        codeBuffer := cb
        code := t.code ++ progs.map progToSectionHOL
        ccRegs := holShiftSeq 1 t.ccRegs
        ccFpRegs := holShiftSeq 1 t.ccFpRegs
        regs := fun r => if r = t.ptrReg then .loc k 0 else
          getRegValue (t.ccRegs 0 r) (if r = t.linkReg then .loc n l else t.regs r)
            WordLocW.word
        fpRegs := fun r => t.ccFpRegs 0 r
        compileOracle := holShiftSeq 1 t.compileOracle } := by
  obtain ⟨codeOk, domOk, secOk⟩ := installCode rel hprogs
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, -, -, -, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, -, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  refine ⟨?_, ?_, h3, h4, h5, h6, h7, h8, codeOk, domOk, secOk, h12, h13, h14, h15, h16, h17,
    h18, fun k' m hk => h19 k' (m + 1) hk, h20, h21, rfl, h23, ?_, fun k' => h25 (k' + 1),
    h26, h27, h28, h29⟩
  · intro r v hv
    simp only [HolFiniteMapExact.updateEq, FUPDATE_HOL, StackSemStateOps.restrictIn] at hv ⊢
    by_cases e1 : r = t.ptrReg
    · rw [if_pos e1] at hv ⊢
      cases hv; rfl
    rw [if_neg e1] at hv ⊢
    by_cases e3 : s.ffiSaveRegs r = true
    · rw [if_pos e3] at hv
      have hcc := h19 r 0 e3
      have hne : r ≠ t.linkReg := by rintro rfl; exact h17 e3
      simp only [hcc, getRegValue, hne, if_false]
      exact h1 r v hv
    · rw [if_neg e3] at hv; simp at hv
  · intro r v hv
    simp [HolFiniteMapExact.empty] at hv
  · funext m
    simp only [holShiftSeq]
    exact congrFun h24 (m + 1)

/-- One LabSem `Install` step with all its checks passing. -/
theorem installStep {t : Flapjack.Compiler.Backend.LabSem.State width C F} {w1 w2 : BitVec width}
    {a b p k : Nat} {bytes : List (BitVec 8)} {cb : WordSemBuffer width 8} {cfg cfg' : C}
    {prog : LabProgHOL width} {ls : List (LabLineHOL width)} {rest : LabProgHOL width}
    (c : Nat)
    (fetch : asmFetchAux t.pc t.code = some (.labAsm .install 0 [] 0))
    (hp : t.regs t.ptrReg = .word w1) (hl : t.regs t.lenReg = .word w2)
    (hk : t.regs t.linkReg = .loc a b)
    (hfl : wordSemBufferFlush t.codeBuffer w1 w2 = some (bytes, cb))
    (hpc : locToPc a b t.code = some p) (ho : t.compileOracle 0 = (cfg, prog))
    (hc : t.compile cfg prog = some (bytes, cfg')) (hprog : prog = ⟨k, ls⟩ :: rest)
    (hcfg : (t.compileOracle 1).1 = cfg') :
    evaluate { t with clock := c + 1 } = evaluate { t with
      pc := p
      codeBuffer := cb
      code := t.code ++ prog
      ccRegs := holShiftSeq 1 t.ccRegs
      ccFpRegs := holShiftSeq 1 t.ccFpRegs
      regs := fun r => if r = t.ptrReg then .loc k 0 else
        getRegValue (t.ccRegs 0 r) (t.regs r) WordLocW.word
      fpRegs := fun r => t.ccFpRegs 0 r
      compileOracle := holShiftSeq 1 t.compileOracle
      clock := c } := by
  rw [evaluate]
  simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hp, hl, hk, hfl, hpc, ho, hc]
  subst hprog
  simp only
  rw [if_pos ⟨rfl, by simpa [holShiftSeq] using hcfg⟩]
  rfl

/-- `Install` case. -/
theorem flattenCorrectInstall (s1 : StackSemStateFiniteExact width C F)
    (ptr len dptr dlen ret : Nat) : FlattenPropWithin (.install ptr len dptr dlen ret : HolProg
        width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_install] at ev
  simp only [Compiler.Backend.StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm .install 0 [] 0, .label n l 0] t1.code := by
    simpa [flattenHOL, appListAppendList] using inst
  obtain ⟨fetch0, i2⟩ := lineAt rfl hinst
  obtain ⟨fetch1, i3⟩ := lineAt rfl i2
  obtain ⟨locL, -⟩ := labelAt i3
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, d13, d14, -, -, -, -, -, -, -, h22, h23, h24, -⟩ :=
    id rel
  have hus := (relNoStack rel).1
  rcases hx : StackSemStateOps.getVar t1.ptrReg s1 with _ | ⟨w1 | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar t1.lenReg s1 with _ | ⟨w2 | ⟨_, _⟩⟩ <;>
    rcases hz : StackSemStateOps.getVar dptr s1 with _ | ⟨w3 | ⟨_, _⟩⟩ <;>
    rcases hw : StackSemStateOps.getVar dlen s1 with _ | ⟨w4 | ⟨_, _⟩⟩ <;>
    simp only [hx, hy, hz, hw] at ev <;> try exact (err ev).elim
  rcases ho : s1.compileOracle 0 with ⟨cfg, progs, bm⟩
  have hprogs : (s1.compileOracle 0).2.1 = progs := by rw [ho]
  simp only [ho, hus, Bool.false_eq_true, if_false] at ev
  rcases hfl : wordSemBufferFlush s1.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩
  · simp only [hfl] at ev; exact (err ev).elim
  simp only [hfl] at ev
  rcases hc : s1.compile cfg progs with _ | ⟨bytes', cfg'⟩
  · simp only [hc] at ev; exact (err ev).elim
  simp only [hc] at ev
  rcases hpr : progs with _ | ⟨⟨k, p0⟩, rest⟩
  · rw [hpr] at ev; exact (err ev).elim
  rw [hpr] at ev
  simp only at ev
  split at ev
  swap; · exact (err ev).elim
  rename_i hv
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  rw [← hpr]
  have ho' : t1.compileOracle 0 = (cfg, progs.map progToSectionHOL) := by
    rw [h24]; simp [ho]
  have hc' : t1.compile cfg (progs.map progToSectionHOL) = some (bytes, cfg') := by
    have := congrFun (congrFun h23 cfg) progs
    rw [← this, hc, hv.1]
  have hcfg : (t1.compileOracle 1).1 = cfg' := by
    rw [h24]; simpa [holShiftSeq] using hv.2.2
  have hmap : progs.map progToSectionHOL = ⟨k, (progToSectionHOL (k, p0)).lines⟩ ::
      rest.map progToSectionHOL := by
    rw [hpr]; simp [progToSection_eq]
  refine ⟨2, { t1 with
      pc := t1.pc + 1 + 1
      codeBuffer := cb
      code := t1.code ++ progs.map progToSectionHOL
      ccRegs := holShiftSeq 1 t1.ccRegs
      ccFpRegs := holShiftSeq 1 t1.ccFpRegs
      regs := fun r => if r = t1.ptrReg then .loc k 0 else
        getRegValue (t1.ccRegs 0 r) (if r = t1.linkReg then .loc n l else t1.regs r)
          WordLocW.word
      fpRegs := fun r => t1.ccFpRegs 0 r
      compileOracle := holShiftSeq 1 t1.compileOracle },
    leafBound rfl (by simp [flattenStepFactor]), fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
        List.prefix_append _ _, ?_, ?_⟩
  · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1 + 1) + 1 by omega, locValueStep _ fetch0 locL]
    refine (installStep (t := { t1 with
        regs := fun key => if key = t1.linkReg then .loc n l else t1.regs key
        pc := t1.pc + 1 }) (w1 := w1) (w2 := w2) (t1.clock + ck1) fetch1
      (by simp [Ne.symm d14, InstCorrect.regOfLookup rel hx])
      (by simp [Ne.symm d13, InstCorrect.regOfLookup rel hy])
      (by simp) (by simpa [← h22] using hfl) locL ho' hc' hmap hcfg).trans ?_
    rfl
  · simp [flattenHOL, appListAppendList, isLabelHOL]
  · rw [hpr] at hprogs
    have := stateRelInstall rel hprogs bm cb s1.dataBuffer k n l (t1.pc + 1 + 1)
    rw [← hpr] at this
    rwa [hus] at this

end

end SteppedFlapjack.StackToLabSteps
