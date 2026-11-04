import Flapjack.Compiler.Backend.LabToTarget.BytesInMemoryFetch
import SteppedFlapjack.LabToTargetSteps.Defs

/-! Adapted copy of `progToBytes_lemma`, `imp_bytesInMemory` and
`imp_bytesInMemory_state` from
`Flapjack/Compiler/Backend/LabToTarget/BytesInMemoryFetch.lean`
(stepped-flapjack#2, phase B). Each conclusion adds that the target line `j`
is a line of the target code, `j ∈ codeLines code2`, so its byte length is at
most `maxLineBytes code2`. The original module is imported by other Flapjack
modules this development needs, so the copies are renamed with a `_mem`
suffix. The `@[hol]` attributes are dropped. Otherwise the statements and
proofs follow the original. -/

/-! Original fetched-instruction byte placement (lab_to_targetProofScript.sml
1155-1258): a fetched source line has a similar, encoding-valid target line
whose bytes lie in memory at its physical position. All code-similarity,
encoding-validity and fetch hypotheses are retained; the machine configuration
is quantified as in the source, which reads only its target configuration. -/
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget

theorem progToBytes_lemma_mem {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (code2 code1 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (i : LabLineHOL width) (pos : Nat) :
    codeSimilar code1 code2 ∧ allEncOk mc.target.config labs ffis pos code2 ∧
      asmFetchAux pc code1 = some i →
    ∃ bs j bs2,
      progToBytes code2 = bs ++ lineBytes j ++ bs2 ∧
      bs.length + pos = posVal pc pos code2 ∧
      bs.length + pos + (lineBytes j).length = posVal (pc + 1) pos code2 ∧
      lineSimilar i j ∧
      lineOk mc.target.config labs ffis (posVal pc pos code2) j ∧
      j ∈ codeLines code2 := by
  induction code2 generalizing code1 pc pos with
  | nil =>
    rintro ⟨hsim, -, hf⟩
    cases code1 with
    | nil => simp [asmFetchAux] at hf
    | cons _ _ => exact hsim.elim
  | cons sec2 rest2 ih =>
    rcases sec2 with ⟨k, lines2⟩
    cases code1 with
    | nil => rintro ⟨hsim, -, -⟩; exact hsim.elim
    | cons sec1 rest1 =>
    rcases sec1 with ⟨k1, lines1⟩
    rintro ⟨⟨hrest, hlines, hk⟩, henc, hf⟩
    simp only at hlines hk
    induction lines2 generalizing lines1 pc pos with
    | nil =>
      cases hlines
      have he : allEncOk mc.target.config labs ffis pos rest2 := by
        rw [allEncOk] at henc; exact henc.2
      have hf' : asmFetchAux pc rest1 = some i := by simpa only [asmFetchAux] using hf
      obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5, h6⟩ := ih rest1 pc pos ⟨hrest, he, hf'⟩
      refine ⟨bs, j, bs2, ?_, ?_, ?_, h4, ?_, by simpa [codeLines] using h6⟩
      · simpa only [progToBytes] using h1
      · simpa only [posVal] using h2
      · simpa only [posVal] using h3
      · simpa only [posVal] using h5
    | cons y ys ihl =>
      cases hlines with
      | cons hxy hxs =>
      rename_i x xs
      rw [allEncOk] at henc
      obtain ⟨hy, htail⟩ := henc
      have hlab := lineSimilar_isLabel x y hxy
      have hlen := lineOk_lineLength _ _ _ _ _ hy
      by_cases hl : isLabelHOL y = true
      · have hx : isLabelHOL x = true := hlab ▸ hl
        have hf' : asmFetchAux pc (⟨k1, xs⟩ :: rest1) = some i := by
          simpa only [asmFetchAux, hx, ↓reduceIte] using hf
        obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5, h6⟩ :=
          ihl pc (pos + lineLength y) xs hxs htail hf'
        have hb : lineBytes y = [] := by cases y <;> simp_all [isLabelHOL, lineBytes]
        rw [hb, List.length_nil] at hlen
        rw [hlen, Nat.add_zero] at h2 h3 h5
        refine ⟨bs, j, bs2, ?_, ?_, ?_, h4, ?_, by simp_all [codeLines]⟩
        · simp only [progToBytes, hb, List.nil_append]; exact h1
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h2
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h3
        · rw [posVal, if_pos hl, hlen, Nat.add_zero]; exact h5
      · have hx : ¬ isLabelHOL x = true := hlab ▸ hl
        cases pc with
        | zero =>
          have hi : i = x := by
            simpa only [asmFetchAux, hx, ↓reduceIte, Bool.false_eq_true,
              Option.some.injEq, eq_comm] using hf
          subst hi
          have hz := posVal_zeroAt mc.target.config labs ffis _ _ (pos + lineLength y) htail
          refine ⟨[], y, progToBytes (⟨k, ys⟩ :: rest2), ?_, ?_, ?_, hxy, ?_,
            by simp [codeLines]⟩
          · simp [progToBytes]
          · simp [posVal, hl]
          · rw [hlen] at hz
            simp only [posVal, if_neg hl, Nat.add_one_sub_one, hlen]
            simp [hz]
          · simpa [posVal, hl] using hy
        | succ n =>
          have hf' : asmFetchAux n (⟨k1, xs⟩ :: rest1) = some i := by
            simpa only [asmFetchAux, hx, ↓reduceIte, Bool.false_eq_true,
              Nat.add_one_ne_zero, Nat.add_one_sub_one] using hf
          obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5, h6⟩ :=
            ihl n (pos + lineLength y) xs hxs htail hf'
          refine ⟨lineBytes y ++ bs, j, bs2, ?_, ?_, ?_, h4, ?_, by simp_all [codeLines]⟩
          · simp only [progToBytes, h1, List.append_assoc]
          · simp only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one, List.length_append]
            omega
          · simp only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one, List.length_append]
            omega
          · simpa only [posVal, if_neg hl, Nat.add_one_ne_zero, ↓reduceIte,
              Nat.add_one_sub_one] using h5

theorem imp_bytesInMemory_mem {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (code1 code2 : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (pc : Nat) (i : LabLineHOL width) (p : BitVec width) (m : BitVec width → BitVec 8)
    (dm dm1 : BitVec width → Prop) :
    codeSimilar code1 code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      asmFetchAux pc code1 = some i ∧ bytesInMemHOL p (progToBytes code2) m dm dm1 →
    ∃ j,
      bytesInMemHOL (p + BitVec.ofNat width (posVal pc 0 code2)) (lineBytes j) m dm dm1 ∧
      lineOk mc.target.config labs ffis (posVal pc 0 code2) j ∧
      posVal (pc + 1) 0 code2 = posVal pc 0 code2 + (lineBytes j).length ∧
      lineSimilar i j ∧ j ∈ codeLines code2 := by
  rintro ⟨hsim, henc, hf, hmem⟩
  obtain ⟨bs, j, bs2, h1, h2, h3, h4, h5, h6⟩ :=
    progToBytes_lemma_mem mc labs ffis code2 code1 pc i 0 ⟨hsim, henc, hf⟩
  rw [h1, bytesInMem_append, bytesInMem_append] at hmem
  simp only [Nat.add_zero] at h2 h3
  refine ⟨j, ?_, h5, by omega, h4, h6⟩
  rw [← h2]; exact hmem.1.2

/-- The fetched-line byte placement specialised to a labSem state; Flapjack
infrastructure shared by the original per-instruction lemmas, which each
begin by instantiating `IMP_bytes_in_memory` at `s1.code` and `s1.pc`. -/
theorem imp_bytesInMemory_state_mem {width : Nat} [NeZero width] {S Q C F : Type}
    (mc : MachineConfig width S Q) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (s1 : LabSem.State width C F) (code2 : LabProgHOL width) (p : BitVec width)
    (t1 : AsmState width) (i : LabLineHOL width)
    (h : codeSimilar s1.code code2 ∧ allEncOk mc.target.config labs ffis 0 code2 ∧
      bytesInMemHOL p (progToBytes code2) t1.mem t1.memDomain
        (fun a => s1.memDomain a = true) ∧
      asmFetch s1 = some i) :
    ∃ j,
      bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) (lineBytes j) t1.mem
        t1.memDomain (fun a => s1.memDomain a = true) ∧
      lineOk mc.target.config labs ffis (posVal s1.pc 0 code2) j ∧
      posVal (s1.pc + 1) 0 code2 = posVal s1.pc 0 code2 + (lineBytes j).length ∧
      lineSimilar i j ∧ j ∈ codeLines code2 :=
  imp_bytesInMemory_mem mc labs ffis s1.code code2 s1.pc i p t1.mem t1.memDomain _
    ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

end SteppedFlapjack.LabToTargetSteps
