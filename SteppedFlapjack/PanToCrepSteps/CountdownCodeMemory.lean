import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import Flapjack.Misc.GetByteSetByte

/-! Construct word memory containing the compiled byte stream. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend

/-- Construct byte memory from a word-backed image. -/
noncomputable def countdownBytesOfWords (words : BitVec 64 → BitVec 64) (a : BitVec 64) : BitVec 8 :=
  HolByte.getByte a (words (holByteAlign a)) false

/-- Update one byte while retaining a word-valued memory. -/
noncomputable def countdownStoreByte (words : BitVec 64 → BitVec 64)
    (address : BitVec 64) (byte : BitVec 8) (a : BitVec 64) : BitVec 64 :=
  if a = holByteAlign address then HolByte.setByte address byte (words a) false else words a

/-- Reading the stored address returns the byte just written. -/
theorem countdownStoreByte_same (words : BitVec 64 → BitVec 64)
    (address : BitVec 64) (byte : BitVec 8) :
    countdownBytesOfWords (countdownStoreByte words address byte) address = byte := by
  simp only [countdownBytesOfWords,countdownStoreByte]
  exact goodDimindex_getByte_setByte address byte _ false (Or.inr rfl)

/-- Storing one byte leaves all other byte addresses unchanged, including
other bytes within the same word. -/
theorem countdownStoreByte_other (words : BitVec 64 → BitVec 64)
    (address target : BitVec 64) (byte : BitVec 8) (different : target ≠ address) :
    countdownBytesOfWords (countdownStoreByte words address byte) target = countdownBytesOfWords words target := by
  simp only [countdownBytesOfWords,countdownStoreByte]
  by_cases h : holByteAlign target = holByteAlign address
  · rw [if_pos h]
    exact getByte_setByte_diff target address byte _ false ⟨Or.inr rfl,different,h⟩
  · rw [if_neg h]

/-- Write a finite byte stream into word memory, starting at a given address. -/
noncomputable def countdownWriteCode (address : BitVec 64) : List (BitVec 8) →
    (BitVec 64 → BitVec 64) → (BitVec 64 → BitVec 64)
  | [], words => words
  | byte :: bytes, words => countdownStoreByte (countdownWriteCode (address + 1) bytes words) address byte

/-- A byte stream shorter than the address space is read back exactly from
its word-backed representation, even when the starting address wraps. -/
theorem countdownWriteCode_get (bytes : List (BitVec 8)) (address : BitVec 64)
    (words : BitVec 64 → BitVec 64) (i : Nat) (hi : i < bytes.length)
    (size : bytes.length < 2^64) :
    countdownBytesOfWords (countdownWriteCode address bytes words) (address + BitVec.ofNat 64 i) = bytes[i] := by
  induction bytes generalizing address i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simpa [countdownWriteCode] using countdownStoreByte_same (countdownWriteCode (address + 1) bs words) address b
    | succ i =>
      have hiTail : i < bs.length := by simpa using hi
      have sizeTail : bs.length < 2^64 := by simp only [List.length_cons] at size; omega
      have offset : address + BitVec.ofNat 64 (i+1) = (address + 1) + BitVec.ofNat 64 i := by
        rw [BitVec.ofNat_add]
        ac_rfl
      have different : address + BitVec.ofNat 64 (i+1) ≠ address := by
        intro h
        have heq : BitVec.ofNat 64 (i+1) = 0 := by
          have h := congrArg (fun x : BitVec 64 => x - address) h
          simpa using h
        have hn := congrArg BitVec.toNat heq
        change (i+1) % 2^64 = 0 at hn
        have bound : i+1 < 2^64 := by simp only [List.length_cons] at size; omega
        rw [Nat.mod_eq_of_lt bound] at hn
        omega
      simp only [countdownWriteCode, List.getElem_cons_succ]
      rw [countdownStoreByte_other _ _ _ _ different,offset]
      exact ih (address + 1) i hiTail sizeTail


/-- Writing code leaves a word untouched if no byte in the stream belongs to it. -/
theorem countdownWriteCode_other_word (bytes : List (BitVec 8)) (address word : BitVec 64)
    (words : BitVec 64 → BitVec 64)
    (outside : ∀ i, i < bytes.length → holByteAlign (address + BitVec.ofNat 64 i) ≠ word) :
    countdownWriteCode address bytes words word = words word := by
  induction bytes generalizing address with
  | nil => rfl
  | cons b bs ih =>
    have head : word ≠ holByteAlign address := by
      have h := outside 0 (by simp)
      apply Ne.symm
      simpa using h
    have tail : ∀ i, i < bs.length → holByteAlign ((address + 1) + BitVec.ofNat 64 i) ≠ word := by
      intro i hi
      have h := outside (i+1) (by simp; omega)
      have offset : address + BitVec.ofNat 64 (i+1) = (address+1) + BitVec.ofNat 64 i := by
        rw [BitVec.ofNat_add]
        ac_rfl
      simpa only [offset] using h
    simp only [countdownWriteCode,countdownStoreByte,if_neg head]
    exact ih (address+1) tail

/-- Build the original sequential byte-loading assertion from indexed facts. -/
theorem bytesInMem_of_indexed (bytes : List (BitVec 8)) (address : BitVec 64)
    (mem : BitVec 64 → BitVec 8) (domain excluded : BitVec 64 → Prop)
    (h : ∀ i, (hi : i < bytes.length) →
      domain (address + BitVec.ofNat 64 i) ∧ ¬ excluded (address + BitVec.ofNat 64 i) ∧
      mem (address + BitVec.ofNat 64 i) = bytes[i]) :
    bytesInMemHOL address bytes mem domain excluded := by
  induction bytes generalizing address with
  | nil => trivial
  | cons b bs ih =>
    have first := h 0 (by simp)
    simp only [BitVec.add_zero] at first
    change domain address ∧ ¬ excluded address ∧ mem address = b at first
    refine ⟨first.1,first.2.1,first.2.2,?_⟩
    apply ih (address + 1)
    intro i hi
    have tail := h (i+1) (by simp; omega)
    have offset : address + BitVec.ofNat 64 (i+1) = (address+1) + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add]
      ac_rfl
    simpa only [offset,List.getElem_cons_succ] using tail

end SteppedFlapjack.PanToCrepSteps
