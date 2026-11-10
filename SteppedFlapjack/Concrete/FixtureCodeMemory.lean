import SteppedFlapjack.Concrete.InitEMemory
import SteppedFlapjack.PanToCrepSteps.CountdownCodeMemory

/-! Load compiled bytes into the init-e-shaped fixture's word-backed memory. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- The fixture's initial word values, before machine code is loaded. -/
def fixtureInitialWords (a : BitVec 64) : BitVec 64 :=
  if a = fixtureBitmapBase then 4 else initialWord a

/-- Write the compiler output at the RISC-V entry address. -/
noncomputable def fixtureLoadedWords (bytes : List (BitVec 8)) : BitVec 64 → BitVec 64 :=
  countdownWriteCode 4096 bytes fixtureInitialWords

/-- The bytes loaded at the entry point are exactly the compiler output. -/
theorem fixtureLoadedWords_get (bytes : List (BitVec 8)) (i : Nat) (hi : i < bytes.length)
    (size : bytes.length < 2^64) :
    countdownBytesOfWords (fixtureLoadedWords bytes) (4096 + BitVec.ofNat 64 i) = bytes[i] :=
  countdownWriteCode_get bytes 4096 fixtureInitialWords i hi size

/-- Loading code below 65536 preserves every word of the init-e heap and bitmap. -/
theorem fixtureLoadedWords_domain (bytes : List (BitVec 8)) (fits : bytes.length ≤ 61440)
    (a : BitVec 64) (domain : fixtureLabDomain a) :
    WordLocW.word (fixtureLoadedWords bytes a) = fixtureLabMemory a := by
  have outside : ∀ i, i < bytes.length → holByteAlign ((4096 : BitVec 64) + BitVec.ofNat 64 i) ≠ a := by
    intro i hi eq
    have addr : ((4096 : BitVec 64) + BitVec.ofNat 64 i).toNat = 4096 + i := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat]
      simp
      omega
    have bound : (holByteAlign ((4096 : BitVec 64) + BitVec.ofNat 64 i)).toNat < 65536 := by
      rw [holByteAlign_toNat (Or.inr rfl),addr]
      have h := Nat.div_mul_le_self (4096+i) 8
      omega
    rw [eq] at bound
    rcases domain with h | h
    · rw [h] at bound
      change (0xa0020018 : BitVec 64).toNat < 65536 at bound
      exact (by decide : ¬ (0xa0020018 : BitVec 64).toNat < 65536) bound
    · simp only [sourceBase] at h
      omega
  rw [fixtureLoadedWords,countdownWriteCode_other_word bytes 4096 a fixtureInitialWords outside]
  by_cases h : a = fixtureBitmapBase <;> simp [fixtureInitialWords,fixtureLabMemory,h]


/-- The loaded memory satisfies the same initializer separation contract. -/
theorem fixtureLoadedMemory_separated (bytes : List (BitVec 8)) (fits : bytes.length ≤ 61440) :
    SetSep.star
      (SetSep.star (Misc.wordList fixtureBitmapBase [(.word 4 : WordLocW 64)])
        (Misc.wordListExists (fixtureBitmapBase+8) 0))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set (fun a => .word (fixtureLoadedWords bytes a),fixtureLabDomain)) := by
  have graph : SetSep.fun2Set (fun a => .word (fixtureLoadedWords bytes a),fixtureLabDomain) =
      SetSep.fun2Set (fixtureLabMemory,fixtureLabDomain) := by
    funext pair
    apply propext
    rcases pair with ⟨a,w⟩
    simp only [SetSep.fun2SetThm]
    constructor <;> intro ⟨h,domain⟩
    · exact ⟨by rw [← fixtureLoadedWords_domain bytes fits a domain]; exact h,domain⟩
    · exact ⟨by rw [fixtureLoadedWords_domain bytes fits a domain]; exact h,domain⟩
  rw [graph]
  exact fixtureLabMemory_separated

end SteppedFlapjack.Concrete
