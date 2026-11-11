import SteppedFlapjack.Concrete.InitEMemory
import SteppedFlapjack.PanToCrepSteps.CountdownCodeMemory

/-! Load compiled bytes into the init-e-shaped fixture's word-backed memory. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Initial word values with a concrete compiler bitmap and arbitrary heap contents. -/
def bitmapInitialWords (bs : List (BitVec 64)) (base : BitVec 64 → BitVec 64) (a : BitVec 64) : BitVec 64 :=
  if bitmapDomain bs.length a then bs[(a.toNat - 0xa0020018) / 8]?.getD 0 else base a

/-- Loading code below the bitmap leaves every bitmap and heap word unchanged. -/
theorem bitmapLoadedWords_domain (address : BitVec 64) (bytes : List (BitVec 8))
    (bs : List (BitVec 64)) (base : BitVec 64 → BitVec 64)
    (fits : address.toNat + bytes.length ≤ 0xa0020018)
    (a : BitVec 64) (domain : bitmapDomain bs.length a ∨
      (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0)) :
    WordLocW.word (countdownWriteCode address bytes (bitmapInitialWords bs base) a) =
      bitmapMemory bs (fun x => .word (base x)) a := by
  have lower : 0xa0020018 ≤ a.toNat := by
    rcases domain with bitmap | heap
    · exact bitmap.1
    · simp only [sourceBase] at heap
      omega
  have outside : ∀ i, i < bytes.length → holByteAlign (address + BitVec.ofNat 64 i) ≠ a := by
    intro i hi eq
    have addr : (address + BitVec.ofNat 64 i).toNat = address.toNat + i := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : i < 2^64)]
      rw [Nat.mod_eq_of_lt (by omega : address.toNat + i < 2^64)]
    have bound : (holByteAlign (address + BitVec.ofNat 64 i)).toNat < 0xa0020018 := by
      rw [holByteAlign_toNat (Or.inr rfl),addr]
      have h := Nat.div_mul_le_self (address.toNat+i) 8
      omega
    rw [eq] at bound
    omega
  rw [countdownWriteCode_other_word bytes address a (bitmapInitialWords bs base) outside]
  by_cases h : bitmapDomain bs.length a <;> simp [bitmapInitialWords,bitmapMemory,h]

/-- The fixture's initial word values, before machine code is loaded. -/
def fixtureInitialWords (a : BitVec 64) : BitVec 64 :=
  if a = fixtureBitmapBase then 4 else initialWord a

theorem bitmapInitialWords_singleton : bitmapInitialWords [4] initialWord = fixtureInitialWords := by
  funext x
  by_cases hd : bitmapDomain 1 x
  · have eq := (bitmapDomain_singleton x).mp hd
    subst x
    simp only [bitmapInitialWords,fixtureInitialWords,List.length_cons,List.length_nil,hd,if_true]
    have hn : fixtureBitmapBase.toNat = 0xa0020018 := by decide
    rw [hn]
    simp
  · have ne : x ≠ fixtureBitmapBase := by
      intro eq
      exact hd ((bitmapDomain_singleton x).mpr eq)
    simp only [bitmapInitialWords,fixtureInitialWords,List.length_cons,List.length_nil,hd,ne,if_false]

/-- Write the compiler output at the RISC-V entry address. -/
noncomputable def fixtureLoadedWords (address : BitVec 64) (bytes : List (BitVec 8)) : BitVec 64 → BitVec 64 :=
  countdownWriteCode address bytes fixtureInitialWords

/-- The bytes loaded at the entry point are exactly the compiler output. -/
theorem fixtureLoadedWords_get (address : BitVec 64) (bytes : List (BitVec 8)) (i : Nat) (hi : i < bytes.length)
    (size : bytes.length < 2^64) :
    countdownBytesOfWords (fixtureLoadedWords address bytes) (address + BitVec.ofNat 64 i) = bytes[i] :=
  countdownWriteCode_get bytes address fixtureInitialWords i hi size

/-- Loading code below the bitmap preserves the init-e heap and bitmap. -/
theorem fixtureLoadedWords_domain (address : BitVec 64) (bytes : List (BitVec 8))
    (fits : address.toNat + bytes.length ≤ 0xa0020018)
    (a : BitVec 64) (domain : fixtureLabDomain a) :
    WordLocW.word (fixtureLoadedWords address bytes a) = fixtureLabMemory a := by
  have domain' : bitmapDomain ([4] : List (BitVec 64)).length a ∨
      (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0) := by
    simpa [bitmapDomain_singleton,fixtureLabDomain] using domain
  have h := bitmapLoadedWords_domain address bytes [4] initialWord fits a domain'
  rw [bitmapInitialWords_singleton,bitmapMemory_singleton] at h
  exact h


/-- Loading a program below the bitmap retains the separated concrete bitmap and heap. -/
theorem bitmapLoadedMemory_separated (address : BitVec 64) (bytes : List (BitVec 8))
    (bs : List (BitVec 64)) (base : BitVec 64 → BitVec 64)
    (codeFits : address.toNat + bytes.length ≤ 0xa0020018)
    (bitmapFits : 0xa0020018 + bs.length*8 ≤ sourceBase) :
    SetSep.star (Misc.wordList fixtureBitmapBase (bs.map WordLocW.word))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set (fun a => .word (countdownWriteCode address bytes (bitmapInitialWords bs base) a),
        fun a => bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a)) := by
  have graph : SetSep.fun2Set
      (fun a => WordLocW.word (countdownWriteCode address bytes (bitmapInitialWords bs base) a),
        fun a => bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a) =
      SetSep.fun2Set (bitmapMemory bs (fun a => .word (base a)),
        fun a => bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a) := by
    funext pair
    apply propext
    rcases pair with ⟨a,w⟩
    simp only [SetSep.fun2SetThm]
    constructor <;> intro ⟨h,domain⟩
    all_goals
      have originalDomain : bitmapDomain bs.length a ∨
          (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0) := by
        simpa [← fixtureLabHeap_addresses] using domain
      have same := bitmapLoadedWords_domain address bytes bs base codeFits a originalDomain
      exact ⟨by first | rw [same] at h; exact h | rw [← same] at h; exact h,domain⟩
  rw [graph]
  exact bitmapMemory_separated bs (fun a => .word (base a)) bitmapFits

/-- The loaded memory satisfies the same initializer separation contract. -/
theorem fixtureLoadedMemory_separated (address : BitVec 64) (bytes : List (BitVec 8))
    (fits : address.toNat + bytes.length ≤ 0xa0020018) :
    SetSep.star
      (SetSep.star (Misc.wordList fixtureBitmapBase [(.word 4 : WordLocW 64)])
        (Misc.wordListExists (fixtureBitmapBase+8) 0))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set (fun a => .word (fixtureLoadedWords address bytes a),fixtureLabDomain)) := by
  have bitmapFits : 0xa0020018 + ([4] : List (BitVec 64)).length*8 ≤ sourceBase := by decide
  have separated := bitmapLoadedMemory_separated address bytes [4] initialWord fits bitmapFits
  rw [bitmapInitialWords_singleton] at separated
  have domain : (fun a => bitmapDomain ([4] : List (BitVec 64)).length a ∨ addresses heapBase fixtureLabHeapWords a) = fixtureLabDomain := by
    funext a
    simp [bitmapDomain_singleton,fixtureLabDomain,← fixtureLabHeap_addresses]
  rw [domain] at separated
  have zero := (WordListExists.wordListExistsThm (β := WordLocW 64) (fixtureBitmapBase+8) 0).1
  rw [zero,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft]
  simpa [fixtureLoadedWords] using separated


end SteppedFlapjack.Concrete
