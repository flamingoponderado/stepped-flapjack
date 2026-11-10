import SteppedFlapjack.Concrete.InitELayout
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
import Flapjack.Misc.Fun2SetUnion
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open SteppedFlapjack.Concrete

namespace SteppedFlapjack.Concrete

/-- The bitmap address in the init-e-shaped layout. -/
def fixtureBitmapBase : BitVec 64 := 0xa0020018
/-- Lab memory agrees with source memory on the heap and stores the compiler bitmap separately. -/
def fixtureLabMemory (a : BitVec 64) : WordLocW 64 :=
  if a = fixtureBitmapBase then .word 4 else .word (initialWord a)
def fixtureLabHeapWords : Nat := (ramEnd-sourceBase)/8

/-- The initializer sees exactly the bitmap word and aligned heap/stack range. -/
def fixtureLabDomain (a : BitVec 64) : Prop :=
  a = fixtureBitmapBase ∨ (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0)
instance (a : BitVec 64) : Decidable (fixtureLabDomain a) := by unfold fixtureLabDomain; infer_instance

theorem fixtureLabHeap_addresses (a : BitVec 64) :
    (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0) ↔ addresses heapBase fixtureLabHeapWords a := by
  rw [mem_addresses]
  constructor
  · intro h
    refine ⟨(a.toNat-sourceBase)/8,?_,?_⟩
    · simp only [sourceBase,ramEnd,ramStart,ramSize] at h
      simp [fixtureLabHeapWords,ramEnd,ramStart,ramSize,sourceBase]
      omega
    · apply BitVec.eq_of_toNat_eq
      change a.toNat = (BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 ((a.toNat-sourceBase)/8) * BitVec.ofNat 64 8).toNat
      rw [BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat]
      simp only [sourceBase,ramEnd,ramStart,ramSize] at h
      simp only [sourceBase]
      omega
  · rintro ⟨i,hi,h⟩
    simp only [fixtureLabHeapWords,ramEnd,ramStart,ramSize,sourceBase] at hi
    change a = BitVec.ofNat 64 sourceBase + BitVec.ofNat 64 i * BitVec.ofNat 64 8 at h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat] at hn
    simp only [sourceBase,ramEnd,ramStart,ramSize]
    simp only [sourceBase] at hn
    omega

theorem fixtureBitmap_outside_heap : ¬ addresses heapBase fixtureLabHeapWords fixtureBitmapBase := by
  rw [← fixtureLabHeap_addresses]
  simp [fixtureBitmapBase,sourceBase]

theorem fixtureLabHeap_fits : 8*fixtureLabHeapWords < 2^64 := by decide

theorem fixtureLabHeap_wordList : Misc.wordListExists heapBase fixtureLabHeapWords
    (SetSep.fun2Set (fixtureLabMemory,addresses heapBase fixtureLabHeapWords)) := by
  exact WordListMemory.wordListExistsAddresses fixtureLabMemory fixtureLabHeapWords heapBase ⟨fixtureLabHeap_fits,Or.inr rfl⟩
theorem fixtureBitmap_wordList : Misc.wordList fixtureBitmapBase [.word 4]
    (SetSep.fun2Set (fixtureLabMemory,fun a => a = fixtureBitmapBase)) := by
  simp only [Misc.wordList,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft,SetSep.one]
  funext entry
  apply propext
  simp [SetSep.fun2Set,fixtureLabMemory]

/-- The real initializer memory layout holds without enumerating the large heap. -/
theorem fixtureLabMemory_separated : SetSep.star
    (SetSep.star (Misc.wordList fixtureBitmapBase [(.word 4 : WordLocW 64)]) (Misc.wordListExists (fixtureBitmapBase+8) 0))
    (Misc.wordListExists heapBase fixtureLabHeapWords)
    (SetSep.fun2Set (fixtureLabMemory,fixtureLabDomain)) := by
  have separated := Misc.Fun2SetUnion.fun2SetDisjointUnion
    (fun a : BitVec 64 => a = fixtureBitmapBase) (addresses heapBase fixtureLabHeapWords) fixtureLabMemory
    (Misc.wordList fixtureBitmapBase [(.word 4 : WordLocW 64)]) (Misc.wordListExists heapBase fixtureLabHeapWords)
    ⟨by intro a ⟨eq,h⟩; subst a; exact fixtureBitmap_outside_heap h, fixtureBitmap_wordList, fixtureLabHeap_wordList⟩
  have graph : SetSep.fun2Set (fixtureLabMemory,fun a => a = fixtureBitmapBase ∨ addresses heapBase fixtureLabHeapWords a) =
      SetSep.fun2Set (fixtureLabMemory,fixtureLabDomain) := by
    have dom : (fun a => a = fixtureBitmapBase ∨ addresses heapBase fixtureLabHeapWords a) = fixtureLabDomain := by
      funext a
      simp only [fixtureLabDomain,fixtureLabHeap_addresses]
    rw [dom]
  rw [graph] at separated
  have zero := (WordListExists.wordListExistsThm (β := WordLocW 64) (fixtureBitmapBase+8) 0).1
  rw [zero,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft]
  exact separated

end SteppedFlapjack.Concrete
