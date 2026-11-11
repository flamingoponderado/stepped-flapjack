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

theorem fixtureLabHeap_fits : 8*fixtureLabHeapWords < 2^64 := by decide

/-- Aligned words occupied by the compiler bitmap. -/
def bitmapDomain (n : Nat) (a : BitVec 64) : Prop :=
  0xa0020018 ≤ a.toNat ∧ a.toNat < 0xa0020018 + n * 8 ∧ a.toNat % 8 = 0
instance (n : Nat) (a : BitVec 64) : Decidable (bitmapDomain n a) := by
  unfold bitmapDomain
  infer_instance

/-- Load a concrete bitmap list before the heap while preserving other memory. -/
def bitmapMemory (bs : List (BitVec 64)) (base : BitVec 64 → WordLocW 64) (a : BitVec 64) : WordLocW 64 :=
  if bitmapDomain bs.length a then .word (bs[(a.toNat - 0xa0020018) / 8]?.getD 0) else base a

theorem bitmapDomain_addresses (n : Nat) (fits : 0xa0020018 + n * 8 ≤ sourceBase) (a : BitVec 64) :
    bitmapDomain n a ↔ addresses fixtureBitmapBase n a := by
  rw [mem_addresses]
  constructor
  · intro h
    refine ⟨(a.toNat - 0xa0020018)/8, ?_, ?_⟩
    · simp only [bitmapDomain,sourceBase] at h fits
      omega
    · apply BitVec.eq_of_toNat_eq
      change a.toNat = (BitVec.ofNat 64 0xa0020018 + BitVec.ofNat 64 ((a.toNat - 0xa0020018)/8) * BitVec.ofNat 64 8).toNat
      rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]
      simp only [bitmapDomain,sourceBase] at h fits
      have : 0xa0020018 + (a.toNat - 0xa0020018) / 8 * 8 < 2^64 := by omega
      rw [Nat.mod_eq_of_lt this]
      omega
  · rintro ⟨i,hi,h⟩
    change a = BitVec.ofNat 64 0xa0020018 + BitVec.ofNat 64 i * BitVec.ofNat 64 8 at h
    have hn := congrArg BitVec.toNat h
    rw [BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat] at hn
    simp only [sourceBase] at fits
    have lt : 0xa0020018 + i*8 < 2^64 := by omega
    rw [Nat.mod_eq_of_lt lt] at hn
    simp only [bitmapDomain]
    omega

theorem bitmapDomain_disjoint (n : Nat) (fits : 0xa0020018+n*8 ≤ sourceBase) (a : BitVec 64)
    (h : bitmapDomain n a) : ¬ addresses heapBase fixtureLabHeapWords a := by
  rw [← fixtureLabHeap_addresses]
  simp only [bitmapDomain] at h
  omega

theorem bitmapMemory_index (bs : List (BitVec 64)) (base : BitVec 64 → WordLocW 64)
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) (i : Nat) (hi : i < bs.length) :
    bitmapMemory bs base (fixtureBitmapBase + BitVec.ofNat 64 i * bytesInWord 64) = .word bs[i] := by
  have dom : bitmapDomain bs.length (fixtureBitmapBase + BitVec.ofNat 64 i * bytesInWord 64) := by
    apply (bitmapDomain_addresses bs.length fits _).mpr
    rw [mem_addresses]
    exact ⟨i,hi,rfl⟩
  have num : (fixtureBitmapBase + BitVec.ofNat 64 i * bytesInWord 64).toNat = 0xa0020018 + i*8 := by
    change (BitVec.ofNat 64 0xa0020018 + BitVec.ofNat 64 i * BitVec.ofNat 64 8).toNat = _
    rw [BitVec.ofNat_mul_ofNat,BitVec.ofNat_add_ofNat,BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [sourceBase] at fits
    omega
  simp [bitmapMemory,dom,num,hi]

theorem bitmapMemory_wordList (bs : List (BitVec 64)) (base : BitVec 64 → WordLocW 64)
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) :
    Misc.wordList fixtureBitmapBase (bs.map WordLocW.word)
      (SetSep.fun2Set (bitmapMemory bs base,bitmapDomain bs.length)) := by
  have bound : fixtureBitmapBase.toNat + (bs.map WordLocW.word).length * (bytesInWord 64).toNat < 2^64 := by
    have hb : fixtureBitmapBase.toNat = 0xa0020018 := by decide
    have hw : (bytesInWord 64).toNat = 8 := by decide
    rw [hb,List.length_map,hw]
    simp only [sourceBase] at fits
    omega
  rw [WordListMemory.wordListSeteq _ _ ⟨Or.inr rfl,bound⟩]
  funext e
  rcases e with ⟨address,value⟩
  apply propext
  simp only [SetSep.fun2SetThm]
  constructor
  · rintro ⟨hm,hd⟩
    have haddr := (bitmapDomain_addresses bs.length fits address).mp hd
    rw [mem_addresses] at haddr
    obtain ⟨i,hi,he⟩ := haddr
    apply List.mem_map.mpr
    refine ⟨i,by simpa using hi,?_⟩
    have val := bitmapMemory_index bs base fits i hi
    have hv : value = .word bs[i] := by rw [← hm,he,val]
    subst address
    subst value
    rw [holEl_eq_getElem i (bs.map WordLocW.word) (by simpa using hi)]
    simp
  · intro member
    obtain ⟨i,hi,he⟩ := List.mem_map.mp member
    have hi' : i < bs.length := by simpa using hi
    have hval := bitmapMemory_index bs base fits i hi'
    have haddr : addresses fixtureBitmapBase bs.length
        (fixtureBitmapBase + BitVec.ofNat 64 i * bytesInWord 64) := by
      rw [mem_addresses]
      exact ⟨i,hi',rfl⟩
    have hadd := (bitmapDomain_addresses bs.length fits _).mpr haddr
    rw [holEl_eq_getElem i (bs.map WordLocW.word) (by simpa using hi')] at he
    simp only [List.getElem_map,Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he.symm
    exact ⟨hval,hadd⟩

/-- Bitmap words and heap words occupy disjoint regions of the initialized memory. -/
theorem bitmapMemory_separated (bs : List (BitVec 64)) (base : BitVec 64 → WordLocW 64)
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) :
    SetSep.star (Misc.wordList fixtureBitmapBase (bs.map WordLocW.word))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set (bitmapMemory bs base,
        fun a => bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a)) := by
  apply Misc.Fun2SetUnion.fun2SetDisjointUnion
    (fun a => bitmapDomain bs.length a) (addresses heapBase fixtureLabHeapWords) (bitmapMemory bs base)
    (Misc.wordList fixtureBitmapBase (bs.map WordLocW.word)) (Misc.wordListExists heapBase fixtureLabHeapWords)
  refine ⟨?_,bitmapMemory_wordList bs base fits,?_⟩
  · intro a ha
    exact bitmapDomain_disjoint bs.length fits a ha.1 ha.2
  · exact WordListMemory.wordListExistsAddresses (bitmapMemory bs base) fixtureLabHeapWords heapBase
      ⟨fixtureLabHeap_fits,Or.inr rfl⟩

theorem bitmapDomain_singleton (a : BitVec 64) : bitmapDomain 1 a ↔ a = fixtureBitmapBase := by
  have fits : 0xa0020018 + 1*8 ≤ sourceBase := by decide
  rw [bitmapDomain_addresses 1 fits,mem_addresses]
  constructor
  · rintro ⟨i,hi,eq⟩
    have : i = 0 := by omega
    subst i
    simpa using eq
  · intro eq
    subst a
    exact ⟨0,by decide,by simp⟩

theorem bitmapMemory_singleton : bitmapMemory [4] (fun a => .word (initialWord a)) = fixtureLabMemory := by
  funext a
  by_cases eq : a = fixtureBitmapBase
  · subst a
    have domain : bitmapDomain ([4] : List (BitVec 64)).length fixtureBitmapBase := by
      simpa using (bitmapDomain_singleton fixtureBitmapBase).mpr rfl
    change bitmapDomain 1 fixtureBitmapBase at domain
    simp only [bitmapMemory,fixtureLabMemory,List.length_cons,List.length_nil,domain,if_true]
    have hn : fixtureBitmapBase.toNat = 0xa0020018 := by decide
    rw [hn]
    simp
  · have domain : ¬ bitmapDomain ([4] : List (BitVec 64)).length a := by
      simpa [bitmapDomain_singleton] using eq
    change ¬ bitmapDomain 1 a at domain
    simp only [bitmapMemory,fixtureLabMemory,List.length_cons,List.length_nil,domain,eq,if_false]

/-- The real initializer memory layout holds without enumerating the large heap. -/
theorem fixtureLabMemory_separated : SetSep.star
    (SetSep.star (Misc.wordList fixtureBitmapBase [(.word 4 : WordLocW 64)]) (Misc.wordListExists (fixtureBitmapBase+8) 0))
    (Misc.wordListExists heapBase fixtureLabHeapWords)
    (SetSep.fun2Set (fixtureLabMemory,fixtureLabDomain)) := by
  have fits : 0xa0020018 + ([4] : List (BitVec 64)).length * 8 ≤ sourceBase := by decide
  have separated := bitmapMemory_separated [4] (fun a => .word (initialWord a)) fits
  rw [bitmapMemory_singleton] at separated
  have domain : (fun a => bitmapDomain ([4] : List (BitVec 64)).length a ∨ addresses heapBase fixtureLabHeapWords a) = fixtureLabDomain := by
    funext a
    simp [bitmapDomain_singleton,fixtureLabDomain,← fixtureLabHeap_addresses]
  rw [domain] at separated
  have zero := (WordListExists.wordListExistsThm (β := WordLocW 64) (fixtureBitmapBase+8) 0).1
  rw [zero,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft]
  simpa using separated

end SteppedFlapjack.Concrete
