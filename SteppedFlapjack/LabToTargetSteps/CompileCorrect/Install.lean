import SteppedFlapjack.LabToTargetSteps.CompileCorrect.CallFfi
import Flapjack.Compiler.Backend.LabToTarget.OracleResidues
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsCorrectness
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.CodeSafety
import Flapjack.Compiler.Backend.LabToTarget.NavigationBounds
import Flapjack.Compiler.Backend.LabToTarget.EncodingValidityClosure

/-! Adapted copy of `Flapjack/Compiler/Backend/LabToTarget/CompileCorrect/Install.lean`
(stepped-flapjack#2, phase B): the `LabAsm Install` case for
`CompileCorrectWithinFor`. The jump to the code-cache entry takes `l` ticks
with `unit * l` at most the line's byte length, which is at most
`maxLineBytes code2`; the cache interference takes one more tick.
`stateRel_install` adds that the installed program's bytes are the flushed
buffer, so its lines fit `lineByteBound` and the tick bound does not grow.
The `@[hol]` attributes are dropped. Otherwise the statements and proofs
follow the original. -/

/-! `LabAsm Install` case of the original `compile_correct`
(lab_to_targetProofScript.sml:8756-9280): the target jumps to the
code-cache entry, where the cache interference installs the flushed buffer
as new code and returns to the link register. Hypotheses are the source
theorem's together with exactly the `evaluate_ind` induction hypothesis of
the case. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabProps

/-- One target step at the code-cache entry: the cache interference runs on
the pointer and length registers (`evaluate_def` in the original). -/
theorem evaluateTarget_ccache {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (c : Nat) (ms : S)
    (hn : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs))
    (hh : mc.target.getPc ms ≠ mc.haltPc) (hc : mc.target.getPc ms = mc.ccachePc) :
    evaluateTargetHOL mc ffi (c + 1) ms =
      evaluateTargetHOL { mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer } ffi c
        (mc.ccacheInterfer 0 (mc.target.getReg ms mc.ptrReg, mc.target.getReg ms mc.lenReg, ms)) := by
  have hn' := hn
  rw [hc] at hn'
  have hh' : mc.ccachePc ≠ mc.haltPc := hc ▸ hh
  simp only [evaluateTargetHOL, hc, hn', hh', ↓reduceIte, applyOracleHOL]

/-- A word location keeps its value under a label-map extension; Flapjack
infrastructure for the label monotonicity steps of the original Install case. -/
theorem wordLocVal_mono {width : Nat} [NeZero width] (p : BitVec width)
    (labs labs' : Spt (Spt Nat))
    (hmono : ∀ a b v, labLookup a b labs = some v → labLookup a b labs' = some v)
    (w : WordLocW width) (x : BitVec width) (h : wordLocVal p labs w = some x) :
    wordLocVal p labs' w = some x := by
  cases w with
  | word v => exact h
  | loc a b =>
    simp only [wordLocVal] at h ⊢
    cases hl : labLookup a b labs with
    | none => rw [hl] at h; cases h
    | some v => rw [hl] at h; rw [hmono a b v hl]; exact h

/-- Byte form of `wordLocVal_mono`. -/
theorem wordLocValByte_mono {width : Nat} [NeZero width] (p : BitVec width)
    (labs labs' : Spt (Spt Nat))
    (hmono : ∀ a b v, labLookup a b labs = some v → labLookup a b labs' = some v)
    (m : BitVec width → WordLocW width) (a : BitVec width) (be : Bool) (x : BitVec 8)
    (h : wordLocValByte p labs m a be = some x) : wordLocValByte p labs' m a be = some x := by
  simp only [wordLocValByte] at h ⊢
  cases hv : wordLocVal p labs (m (holByteAlign a)) with
  | none => rw [hv] at h; cases h
  | some v => rw [hv] at h; rw [wordLocVal_mono p labs labs' hmono _ _ hv]; exact h

/-- The complete relation after installing the flushed code buffer: the
source code grows by the compiled section list, the code buffer is flushed,
the pointer register holds the new section's start label, other registers and
FP registers take the cache oracle's values, the compile oracle advances, and
the label map is the compiler's new one. This is the `state_rel` part of the
original Install case. -/
theorem stateRel_install {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 ms' : S}
    (h : stateRel (mc, code2, labs, p) s1 t1 ms1)
    (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat)
    (hfetch : asmFetch s1 = some (.labAsm .install w bytes n))
    (start finish : BitVec width) (n1 n2 newPc : Nat) (cb : WordSemBuffer width 8)
    (cfg cfg' : Config) (k : Nat) (lines : List (LabLineHOL width)) (rest : LabProgHOL width)
    (flushed : List (BitVec 8))
    (hptr : s1.regs s1.ptrReg = .word start)
    (hlink : s1.regs s1.linkReg = .loc n1 n2)
    (hflush : wordSemBufferFlush s1.codeBuffer start finish = some (flushed, cb))
    (hloc : locToPc n1 n2 s1.code = some newPc)
    (hor : s1.compileOracle 0 = (cfg, ⟨k, lines⟩ :: rest))
    (hcomp : s1.compile cfg (⟨k, lines⟩ :: rest) = some (flushed, cfg'))
    (hcfg' : (s1.compileOracle 1).1 = cfg')
    (htrel : targetStateRel mc.target
      { t1 with
        regs := fun a => if a = s1.ptrReg then t1.regs s1.ptrReg
          else getRegValue (s1.ccRegs 0 a) (t1.regs a) id
        fpRegs := fun r => s1.ccFpRegs 0 r
        pc := t1.regs s1.linkReg } ms') :
    ∃ secList, progToBytes secList = s1.codeBuffer.buffer ∧
      stateRel ({ mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer },
        code2 ++ secList, cfg'.labels, p)
      { s1 with
        pc := newPc
        codeBuffer := cb
        code := s1.code ++ ⟨k, lines⟩ :: rest
        ccRegs := holShiftSeq 1 s1.ccRegs
        ccFpRegs := holShiftSeq 1 s1.ccFpRegs
        regs := fun r => if r = s1.ptrReg then .loc k 0
          else getRegValue (s1.ccRegs 0 r) (s1.regs r) WordLocW.word
        fpRegs := fun r => s1.ccFpRegs 0 r
        compileOracle := holShiftSeq 1 s1.compileOracle
        clock := s1.clock - 1 }
      { t1 with
        regs := fun a => if a = s1.ptrReg then t1.regs s1.ptrReg
          else getRegValue (s1.ccRegs 0 a) (t1.regs a) id
        fpRegs := fun r => s1.ccFpRegs 0 r
        pc := t1.regs s1.linkReg } ms' := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53⟩ := h
  -- the code contains an Install, so it has no shared-memory instructions
  have hfj := codeSimilar_asmFetchAux s1.pc s1.code code2 c49
  rw [show asmFetchAux s1.pc s1.code = asmFetch s1 from rfl, hfetch] at hfj
  obtain ⟨j, hj, hsimj⟩ : ∃ j, asmFetchAux s1.pc code2 = some j ∧
      lineSimilar (.labAsm .install w bytes n) j := by
    revert hfj
    cases asmFetchAux s1.pc code2 with
    | none => intro h; cases h
    | some j => intro h; cases h; exact ⟨j, rfl, by assumption⟩
  have hnoInst : ¬ noInstall code2 := by
    intro hni
    cases j with
    | label => exact hsimj.elim
    | asm => exact hsimj.elim
    | labAsm a w' b' l' =>
      simp only [lineSimilar] at hsimj
      subst hsimj
      exact hni s1.pc w' b' l' hj
  have hnsm : noShareMemInst code2 := (c53.resolve_right hnoInst).1
  -- the oracle's first program and configuration
  have ho0 := c19 hnsm 0
  rw [hor] at ho0
  obtain ⟨hgood0, hnsm0, hk0⟩ := ho0
  obtain ⟨hlabs0, hpos0, hffis0⟩ := hk0 rfl
  rw [c18] at hcomp
  simp only [compileLab, hffis0] at hcomp
  split at hcomp
  rotate_left
  · cases hcomp
  rename_i hsub
  split at hcomp
  rotate_left
  · cases hcomp
  rename_i secList l1 hrm
  simp only [Option.some.injEq, Prod.mk.injEq] at hcomp
  obtain ⟨rfl, rfl⟩ := hcomp
  -- correctness of the label removal for the installed program
  obtain ⟨hEnc, hsim, -, hl1even, hmono, hloc1⟩ := removeLabels_correct cfg.initClock
    mc.target.config cfg.pos cfg.labels mc.ffiNames _ secList l1
    ⟨hrm, c46, hgood0.1, hgood0.2.1, hgood0.2.2.1, hgood0.2.2.2.1, hgood0.2.2.2.2.1,
      hgood0.2.2.2.2.2.1, hgood0.2.2.2.2.2.2, by rw [hpos0]; exact c23,
      fun sid lid => by
        rw [hlabs0]
        cases hl : labLookup sid lid labs with
        | none => trivial
        | some v => exact c20 sid lid v hl⟩
  rw [hlabs0] at hmono
  rw [hpos0] at hEnc hloc1
  have hshm := noShareMem_getShmemInfo secList (progToBytes code2).length [] []
    (codeSimilar_noShareMem _ _ ⟨hsim, hnsm0⟩)
  -- the flushed buffer is exactly the compiled bytes
  simp only [wordSemBufferFlush] at hflush
  split at hflush
  rotate_left
  · cases hflush
  rename_i hfl
  obtain ⟨hstartpos, hfinishpos⟩ := hfl
  simp only [Option.some.injEq, Prod.mk.injEq] at hflush
  obtain ⟨hbuf, rfl⟩ := hflush
  have hL : finish = s1.codeBuffer.position +
      BitVec.ofNat width (progToBytes secList).length := by
    rw [← hfinishpos, hbuf]; simp
  -- code facts
  have hlz := allEncOk_implies_secLabelZero _ _ _ _ _ hEnc
  have hsl1 : ∀ sec ∈ s1.code, secLabelsOk sec :=
    codeSimilar_secLabelsOk code2 s1.code ⟨c48, codeSimilar_sym _ _ c49⟩
  have hlenEq := codeSimilar_lenNoLab _ _ c49
  have hlenP := allEncOk_lengthProgToBytes code2 () _ _ _ _ c47
  have hpv : ∀ x, x ≤ (code2.map (fun sec => lenNoLab sec.lines)).sum →
      posVal x 0 (code2 ++ secList) = posVal x 0 code2 := by
    intro x hx; rw [posVal_append code2 x 0 secList hlz, if_pos hx]
  have hbnd : ∀ a b x, locToPc a b s1.code = some x →
      x ≤ (code2.map (fun sec => lenNoLab sec.lines)).sum := by
    intro a b x hx; rw [← hlenEq]; exact locToPc_bound _ a b x ⟨hsl1, hx⟩
  -- the Install line forces the MMIO boundary to the whole name list
  obtain ⟨i, hi, -⟩ := id c15
  obtain ⟨w', b', l', hj'⟩ : ∃ w' b' l', asmFetchAux s1.pc code2 = some (.labAsm .install w' b' l') := by
    cases j with
    | label => exact hsimj.elim
    | asm => exact hsimj.elim
    | labAsm a w' b' l' =>
      simp only [lineSimilar] at hsimj
      subst hsimj
      exact ⟨w', b', l', hj⟩
  have hiEq : i = mc.ffiNames.length := noShareMem_lemma mc.ffiNames i s1.pc code2 _ _ _ ⟨hi, hj', c53⟩
  have htake : mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames)) = mc.ffiNames := by
    rw [hi, hiEq]; simp [holThe]
  rw [htake] at c47
  have hlinkv : t1.regs s1.linkReg = p + BitVec.ofNat width (posVal newPc 0 code2) := by
    have := c30 s1.linkReg
    rw [hlink] at this
    simp only [wordLocVal, c28 n1 n2 newPc hloc, Option.some.injEq] at this
    exact this.symm
  have hnsmAll : noShareMemInst (code2 ++ secList) :=
    noShareMem_append code2 secList ⟨hnsm, codeSimilar_noShareMem _ _ ⟨hsim, hnsm0⟩⟩
  refine ⟨secList, hbuf.symm, htrel, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, fun ms2 t k' a1 a2 hh => c17 ms2 t (k' + 1) a1 a2 hh, c18, ?_, hl1even,
    c21, ?_, ?_, c24, c25, c26, c27, ?_, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, trivial, ?_, ?_,
    c38, c39, c40, ?_, c42, c43, c44, c45, c46, ?_, ?_, codeSimilar_append _ _ _ _ ⟨c49, hsim⟩,
    ?_, ?_, c52, ?_⟩
  -- 19: the advanced compile oracle
  · intro _ k'
    have h := c19 hnsm (k' + 1)
    simp only [holShiftSeq]
    rcases hk : s1.compileOracle (k' + 1) with ⟨c, code⟩
    rw [hk] at h
    obtain ⟨hg, hn, -⟩ := h
    refine ⟨hg, hn, fun h0 => ?_⟩
    subst h0
    have hc : c = _ := (congrArg Prod.fst hk).symm.trans hcfg'
    subst hc
    rw [hpos0]
    simp [progToBytes_append, hshm, Nat.add_comm]
  -- 22: FFI names of the extended code
  · rw [findFfiNames_append]
    simp only [Misc.listSubset, List.all_eq_true, decide_eq_true_eq, List.mem_filter,
      List.mem_append] at c22 hsub ⊢
    rintro x ⟨hx | hx, hext⟩
    · exact hsub x hx
    · exact c22 x ⟨hx.1, hext⟩
  -- 23: even program length
  · rw [progToBytes_append, List.length_append]
    have := allEncOk_progToBytes_even secList _ _ _ _ ⟨c23, hEnc⟩
    omega
  -- 28: label positions of the extended code
  · intro a b x2 hx
    rw [locToPc_append a b s1.code _ (fun sec hs => (List.mem_append.mp hs).elim
      (hsl1 sec) (hgood0.2.1 sec))] at hx
    cases h1 : locToPc a b s1.code with
    | some x =>
      rw [h1] at hx
      rw [← Option.some.inj hx, hpv x (hbnd a b x h1)]; exact hmono _ _ _ (c28 a b x h1)
    | none =>
      rw [h1] at hx
      cases h2 : locToPc a b (⟨k, lines⟩ :: rest) with
      | none => rw [h2] at hx; cases hx
      | some x' =>
        rw [h2] at hx; cases hx
        rw [hloc1 a b x' h2, hlenEq, posVal_append code2 _ 0 secList hlz]
        split
        · have hx0 : x' = 0 := by omega
          subst hx0
          rw [Nat.zero_add, posVal_acc, Nat.zero_add, hlenP, posVal_zero _ _ _ _ _ hEnc]
        · rw [Nat.add_sub_cancel, Nat.zero_add, hlenP]
  -- 30: registers
  · intro r
    dsimp only
    by_cases hr : r = s1.ptrReg
    · subst hr
      rw [if_pos rfl, if_pos rfl]
      have hk0 : locToPc k 0 (⟨k, lines⟩ :: rest) = some 0 := by rw [locToPc.eq_def]; simp
      simp only [wordLocVal, hloc1 k 0 0 hk0, posVal_zero _ _ _ _ _ hEnc]
      rw [wordLocVal_word_target (c30 _) hptr, ← hstartpos, c34]
    · simp only [hr, ↓reduceIte]
      cases hcc : s1.ccRegs 0 r with
      | some v => simp [getRegValue, wordLocVal]
      | none => simpa [getRegValue] using wordLocVal_mono p labs l1 hmono _ _ (c30 r)
  -- 31: memory
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := c31 a ha
    exact ⟨h1, h2, wordLocValByte_mono p labs l1 hmono _ _ _ _ h3⟩
  -- 32: code buffer space
  · intro m hm
    have := c32 m hm
    simp only [List.length_nil, Nat.zero_add]
    rw [hL, BitVec.add_assoc, ← BitVec.ofNat_add, ← hbuf]
    exact this
  -- 33: program bytes
  · rw [progToBytes_append, bytesInMem_append]
    exact ⟨c33, by rw [← c34, ← hbuf]; exact c35⟩
  -- 34: buffer position
  · rw [hL, c34, progToBytes_append, List.length_append, BitVec.ofNat_add, BitVec.add_assoc]
  -- 36: length bound
  · simp only [progToBytes_append, List.length_append, List.length_nil, Nat.add_zero]
    rw [hbuf] at c36
    omega
  -- 37: FFI entries are outside the buffer
  · intro bn hbn
    simp only [List.length_nil, Nat.zero_add] at hbn
    have := c37 (s1.codeBuffer.buffer.length + bn) (by omega)
    rw [hL, BitVec.add_assoc, ← BitVec.ofNat_add, ← hbuf]
    exact this
  -- 41: PC
  · rw [hlinkv, hpv newPc (hbnd n1 n2 newPc hloc)]
  -- 47: encodings of the extended code
  · rw [htake]
    exact allEncOk_append _ _ _ _ _ _
      ⟨allEncOk_extendLabels _ _ _ _ _ _ ⟨hmono, c47⟩, by simpa using hEnc⟩
  -- 48: section labels
  · intro sec hs
    rcases List.mem_append.mp hs with h | h
    · exact c48 sec h
    · exact codeSimilar_secLabelsOk _ _ ⟨hgood0.2.1, hsim⟩ sec h
  -- 50: shared-memory relation
  · unfold shareMemStateRel at c50 ⊢; exact c50
  -- 51: shared-memory code relation
  · obtain ⟨d1, d2, d3, d4⟩ := c51
    refine ⟨fun pc op re a inst len i' h =>
      absurd h.1 (hnsmAll pc op re a inst len), ?_, d3, d4⟩
    rintro pc line ⟨hf, hns⟩ x hx ⟨a, hxa, halen⟩
    by_cases hpc : pc < numPcs code2
    · rw [asmFetchAux_append1 pc code2 secList hpc] at hf
      rw [posVal_appendPrefix pc code2 secList hpc] at hxa
      exact d2 pc line ⟨hf, hns⟩ x hx ⟨a, hxa, halen⟩
    · obtain ⟨pc', rfl⟩ : ∃ pc', pc = pc' + numPcs code2 := ⟨pc - numPcs code2, by omega⟩
      rw [asmFetchAux_append2] at hf
      rw [posVal_appendSuffix _ _ _ _ code2 pc' secList c47] at hxa
      have hsucc := asmFetchAux_posVal_successor pc' 0 secList _ _ _ _ line ⟨hEnc, hf⟩
      have hbd := posVal_bound (pc' + 1) 0 secList _ l1 _ _ hEnc
      refine c37 (posVal pc' 0 secList + a) (by rw [hbuf]; omega) ?_
      have hxe : s1.codeBuffer.position + BitVec.ofNat width (posVal pc' 0 secList + a) = x := by
        rw [hxa, c34]
        simp only [BitVec.ofNat_add]
        ring
      rw [hxe]; exact hx
  -- 53: no shared memory in the extended code
  · exact Or.inl ⟨hnsmAll, (c53.resolve_right hnoInst).2⟩

theorem compileCorrect_install {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    {unit : Nat} {steps : HolAsm width → Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F)
    (w : BitVec width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.labAsm .install w bytes n))
    (ih : ∀ (start finish : BitVec width) (n1 n2 : Nat) (flushed : List (BitVec 8))
        (cb : WordSemBuffer width 8) (newPc : Nat) (cfg : Config) (prog : LabProgHOL width)
        (k : Nat) (lines : List (LabLineHOL width)) (rest : LabProgHOL width) (cfg' : Config),
      s1.regs s1.ptrReg = .word start → s1.regs s1.lenReg = .word finish →
      s1.regs s1.linkReg = .loc n1 n2 →
      wordSemBufferFlush s1.codeBuffer start finish = some (flushed, cb) →
      locToPc n1 n2 s1.code = some newPc →
      s1.compileOracle 0 = (cfg, prog) → prog = ⟨k, lines⟩ :: rest →
      s1.compile cfg prog = some (flushed, cfg') → (s1.compileOracle 1).1 = cfg' →
      CompileCorrectWithinFor S Q unit steps { s1 with
        pc := newPc
        codeBuffer := cb
        code := s1.code ++ prog
        ccRegs := holShiftSeq 1 s1.ccRegs
        ccFpRegs := holShiftSeq 1 s1.ccFpRegs
        regs := fun r => if r = s1.ptrReg then .loc k 0
          else getRegValue (s1.ccRegs 0 r) (s1.regs r) WordLocW.word
        fpRegs := fun r => s1.ccFpRegs 0 r
        compileOracle := holShiftSeq 1 s1.compileOracle
        clock := s1.clock - 1 }) :
    CompileCorrectWithinFor S Q unit steps s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hec, hfit, hrel⟩
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i start finish n1 n2 hptr hlen hlink
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i flushed cb newPc hflush hloc
  rcases hor : s1.compileOracle 0 with ⟨cfg, prog⟩
  simp only [hor] at hev
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i bytes' cfg' k lines rest hcomp
  split at hev
  rotate_left
  · exact absurd (Prod.mk.inj hev).1.symm hres
  rename_i hvalid
  obtain ⟨rfl, hcfg'⟩ := hvalid
  obtain ⟨c1, c2, -, -, c5, c6, c7, c8, c9, -, -, -, -, -, -, -, c17, -, -, -, -, -, -, -, c25,
    c26, -, -, -, -, -, -, -, -, -, -, -, -, ht1f, -, htpc, -⟩ := id hrel
  -- the target line is a jump to the code-cache entry
  obtain ⟨w', bytesL, len', hok, hmem, hpos, hdis, hbl⟩ := fetchedLabAsmLine hrel hfetch
  simp only [lineOk] at hok
  obtain ⟨l, ms2, hl⟩ := stepOfLine s1.ffi hrel hec hfit _ bytesL hmem hok.1 hok.2.2 hdis
    (by simp [asmUpd, jumpToOffset, AsmSem.updPc, ht1f])
  have hjpc : t1.pc + (0 - BitVec.ofNat width (posVal s1.pc 0 code2 + 2 * ffiOffset)) =
      p - BitVec.ofNat width (2 * ffiOffset) := by
    rw [htpc, BitVec.ofNat_add]; ring
  have hts : targetStateRel mc.target
      { t1 with pc := p - BitVec.ofNat width (2 * ffiOffset) } ms2 := by
    have := (hl 0).2.2.1
    simp only [asmUpd, jumpToOffset, AsmSem.updPc, hjpc] at this
    exact this
  obtain ⟨-, hgpc, -, hgreg, -⟩ := id hts
  have hpc2 : mc.target.getPc ms2 = mc.ccachePc := hgpc.trans c26
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms2) ∧
      mc.target.getPc ms2 ∉ mc.ffiEntryPcs) := fun h => c5 (hpc2 ▸ h.1)
  have hhalt : mc.target.getPc ms2 ≠ mc.haltPc := by
    rw [hpc2, ← c25, ← c26]
    intro h
    rcases c2 with hw | hw <;> subst hw <;> simp only [ffiOffset] at h <;> bv_omega
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      mc.target.getReg ms2 r = t1.regs r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact hgreg r hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, c28,
    -, c30, -⟩ := id hrel
  have hstart : mc.target.getReg ms2 mc.ptrReg = start := by
    rw [c7, hreg _ c6]; exact wordLocVal_word_target (c30 _) hptr
  have hfinish : mc.target.getReg ms2 mc.lenReg = finish := by
    rw [c9, hreg _ c8]; exact wordLocVal_word_target (c30 _) hlen
  have hlinkv : t1.regs s1.linkReg = p + BitVec.ofNat width (posVal newPc 0 code2) := by
    have := c30 s1.linkReg
    rw [hlink] at this
    simp only [wordLocVal, c28 n1 n2 newPc hloc, Option.some.injEq] at this
    exact this.symm
  -- the cache interference returns to the link register with the oracle's registers
  obtain ⟨hres1, hres2⟩ := oracleTie_ccacheResidues mc (shiftInterfer l mc) ms1 s1 ms2 l t1
    ⟨ht, fun k => (hl k).2.1, rfl, rfl, rfl, rfl, hn, hhalt, hpc2⟩
  rw [hstart, hfinish] at hres1 hres2
  have htrel := c17 ms2 t1 0 start finish
    ⟨hts, by rw [hlinkv]; exact stateRel_aligned_target hrel (encoderCorrect_of_within hec) newPc⟩
  dsimp only at htrel
  have hregs : (fun a => if a ∈ mc.calleeSavedRegs ∨ a = s1.ptrReg ∨
      ¬ a < mc.target.config.regCount ∨ a ∈ mc.target.config.avoidRegs then t1.regs a
      else mc.target.getReg (mc.ccacheInterfer 0 (start, finish, ms2)) a) =
      fun a => if a = s1.ptrReg then t1.regs s1.ptrReg
        else getRegValue (s1.ccRegs 0 a) (t1.regs a) id := by
    have h1 := hres1
    rw [c7] at h1
    rw [← h1]
    funext a
    by_cases ha : a = s1.ptrReg
    · subst ha
      simpa using congrFun h1 s1.ptrReg
    · simp [ha]
  rw [hregs, ← hres2] at htrel
  obtain ⟨secList, hsecb, hrel'0⟩ := stateRel_install hrel w bytes n hfetch start finish n1 n2
    newPc cb cfg cfg' k lines rest flushed hptr hlink hflush hloc hor hcomp hcfg' htrel
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel'0
  -- the oracle tie after the cache interference
  have ht2 := oracleTie_shiftInterfer mc ms1 ms2 s1 l ⟨ht, fun k => (hl k).2.1⟩
  have hnext := nextInterferenceCache (shiftInterfer l mc) s1.ffi ms2 ⟨hn, hhalt, hpc2⟩
  have ht3 : oracleTie { shiftInterfer l mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer }
      (mc.ccacheInterfer 0 (start, finish, ms2))
      { s1 with
        pc := newPc
        codeBuffer := cb
        code := s1.code ++ ⟨k, lines⟩ :: rest
        ccRegs := holShiftSeq 1 s1.ccRegs
        ccFpRegs := holShiftSeq 1 s1.ccFpRegs
        regs := fun r => if r = s1.ptrReg then .loc k 0
          else getRegValue (s1.ccRegs 0 r) (s1.regs r) WordLocW.word
        fpRegs := fun r => s1.ccFpRegs 0 r
        compileOracle := holShiftSeq 1 s1.compileOracle
        clock := s1.clock - 1 } := by
    have hnext' : nextInterference (shiftInterfer l mc) s1.ffi ms2 = some
        (.ccApp start finish ms2 (mc.ccacheInterfer 0 (start, finish, ms2)),
          { shiftInterfer l mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer }, s1.ffi) := by
      rw [hnext]
      simp only [shiftInterfer] at hstart hfinish ⊢
      rw [hstart, hfinish]
    exact oracleTie_cacheNext (shiftInterfer l mc) ms2 s1 _ start finish ms2 _ _ s1.ffi
      ⟨ht2, hnext', rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨k', ms3, hkb, hk⟩ := ih start finish n1 n2 _ cb newPc cfg _ k lines rest cfg' hptr hlen
    hlink hflush hloc hor rfl hcomp hcfg' res _ s2 _ _ _ _ p ⟨ht3, hev, hres, hec, hfit, hrel'⟩
  obtain ⟨-, hcbuf, hcsp⟩ := wordSemBufferFlush_some hflush
  have hL : labTickBound unit (code2 ++ secList) cb ≤ labTickBound unit code2 s1.codeBuffer :=
    labTickBound_mono (lineByteBound_install (by rw [hsecb]) (by rw [hcbuf, hcsp]; simp))
  refine ⟨k' + l, ms3, tick_step_bound_succ hclock (tick_bound_mono hL hkb)
    (le_labTickBound_of_bytes hfit.1 (hl 0).2.2.2.2 hbl), ?_⟩
  rw [show s1.clock + (k' + l) = (s1.clock + k') + l by omega, (hl _).1,
    show s1.clock + k' = (s1.clock - 1 + k') + 1 by omega,
    evaluateTarget_ccache (shiftInterfer l mc) s1.ffi _ ms2 hn hhalt hpc2]
  simp only [shiftInterfer, hstart, hfinish] at hk ⊢
  exact hk

end SteppedFlapjack.LabToTargetSteps
