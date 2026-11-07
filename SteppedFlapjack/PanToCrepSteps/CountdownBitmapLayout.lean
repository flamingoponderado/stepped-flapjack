import SteppedFlapjack.PanToCrepSteps.CountdownExampleLayout
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListMemory

/-! Concrete bitmap address range for the countdown initializer. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

set_option maxRecDepth 32768 in
/-- The aligned addresses of the concrete bitmap interval are exactly the
8192 words used by the original Stack initializer. -/
theorem countdownExample_bitmapAddresses :
    (fun a : BitVec 64 => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true) =
      addresses (131072 : BitVec 64) 8192 := by
  funext a
  apply propext
  rw [mem_addresses]
  rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]
  simp only [countdownExampleBitmapsDomain,decide_eq_true_eq]
  constructor
  · rintro ⟨aligned,lo,hi⟩
    let i := (a.toNat - 131072) / 8
    have hi : i < 8192 := by dsimp [i]; omega
    refine ⟨i, hi, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,bytesInWord]
    have eq : 131072 + i * 8 = a.toNat := by dsimp [i]; omega
    simp only [Nat.reduceDiv, Nat.reducePow, Nat.reduceMod, show (131072 : BitVec 64).toNat = 131072 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : i < 18446744073709551616)]
    rw [Nat.mod_eq_of_lt (by omega : i * 8 < 18446744073709551616)]
    rw [Nat.mod_eq_of_lt (by omega : 131072 + i * 8 < 18446744073709551616)]
    exact eq.symm
  · rintro ⟨i,hi,rfl⟩
    simp only [BitVec.toNat_add,BitVec.toNat_mul,BitVec.toNat_ofNat,bytesInWord]
    simp only [Nat.reduceDiv,Nat.reducePow,Nat.reduceMod, show (131072 : BitVec 64).toNat = 131072 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : i < 18446744073709551616)]
    rw [Nat.mod_eq_of_lt (by omega : i * 8 < 18446744073709551616)]
    rw [Nat.mod_eq_of_lt (by omega : 131072 + i * 8 < 18446744073709551616)]
    omega

/-- Store the bitmap word while preserving all other backing words. -/
def countdownExampleBitmapBacking (bitmap : BitVec 64) (rest : BitVec 64 → BitVec 64)
    (a : BitVec 64) : BitVec 64 :=
  if a = 131072 then bitmap else rest a

set_option maxRecDepth 32768 in
/-- One emitted bitmap followed by 8191 free words fills the concrete bitmap
region whenever the backing memory contains that bitmap at its base. -/
theorem countdownExample_singleBitmapLayout (rest : BitVec 64 → BitVec 64) (bitmap : BitVec 64)
    (atBase : rest 131072 = bitmap) :
    SetSep.star (Misc.wordList (131072 : BitVec 64) ([bitmap].map WordLocW.word))
      (Misc.wordListExists ((131072 : BitVec 64) + 8 * BitVec.ofNat 64 1) 8191)
      (SetSep.fun2Set ((fun a => WordLocW.word (rest a)),
        fun a => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true)) := by
  have all := WordListMemory.wordListExistsAddresses (fun a : BitVec 64 => WordLocW.word (rest a))
    8192 (131072 : BitVec 64) ⟨by decide, Or.inr rfl⟩
  rw [← countdownExample_bitmapAddresses] at all
  have split := all
  change Misc.wordListExists (131072 : BitVec 64) (1 + 8191) _ at split
  rw [WordListMemory.wordListExistsAdd] at split
  obtain ⟨left,right,partition,first,last⟩ := split
  obtain ⟨xs, hx⟩ := first
  obtain ⟨hx, len⟩ := (StackRemove.WordListExists.starCond _ _ _).mp hx
  cases xs with
  | nil => simp at len
  | cons value tail =>
    have tailNil : tail = [] := List.length_eq_zero_iff.mp (by simpa using len)
    subst tail
    have belongs : left (131072, value) := by
      rcases hx with ⟨head, empty, part, one, _⟩
      have hm : head (131072,value) := by rw [one]
      rw [← part.1]
      exact Or.inl hm
    have graph : SetSep.fun2Set ((fun a : BitVec 64 => WordLocW.word (rest a)),
        fun a => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true) (131072,value) := by
      rw [← partition.1]
      exact Or.inl belongs
    have eq := ((SetSep.fun2SetThm _ _ _ _).mp graph).1
    have valueEq : value = WordLocW.word (rest 131072) := eq.symm
    subst value
    rw [atBase] at hx
    exact ⟨left,right,partition,by simpa using hx,by simpa [bytesInWord] using last⟩

end SteppedFlapjack.PanToCrepSteps
