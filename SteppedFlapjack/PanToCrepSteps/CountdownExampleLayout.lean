import SteppedFlapjack.PanToCrepSteps.CountdownByteDomain
import SteppedFlapjack.PanToCrepSteps.CountdownStackInit

/-! Concrete heap metadata for the countdown machine. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Install the five initializer metadata words. All other words are supplied
by the caller, allowing code and bitmap data to be loaded independently. -/
def countdownExampleWords (bytes : List (BitVec 8)) (cbspace dataSp : Nat)
    (bitmaps : List (BitVec 64)) (rest : BitVec 64 → BitVec 64) (a : BitVec 64) : BitVec 64 :=
  if a = 65536 then 131072
  else if a = 65544 then 131072 + 8 * BitVec.ofNat 64 bitmaps.length
  else if a = 65552 then 131072 + 8 * BitVec.ofNat 64 dataSp + 8 * BitVec.ofNat 64 bitmaps.length
  else if a = 65560 then 4096 + BitVec.ofNat 64 bytes.length
  else if a = 65568 then 4096 + BitVec.ofNat 64 cbspace + BitVec.ofNat 64 bytes.length
  else rest a

/-- The initializer metadata does not change words outside its five slots. -/
theorem countdownExampleWords_other (bytes : List (BitVec 8)) (cbspace dataSp : Nat)
    (bitmaps : List (BitVec 64)) (rest : BitVec 64 → BitVec 64) (a : BitVec 64)
    (h : a.toNat < 65536 ∨ 65576 ≤ a.toNat) :
    countdownExampleWords bytes cbspace dataSp bitmaps rest a = rest a := by
  simp only [countdownExampleWords]
  have ne (n : Nat) (hn : 65536 ≤ n ∧ n < 65576) : a ≠ BitVec.ofNat 64 n := by
    intro eq
    have he := congrArg BitVec.toNat eq
    simp only [BitVec.toNat_ofNat] at he
    have mod : n % 2^64 = n := Nat.mod_eq_of_lt (by omega)
    rw [mod] at he
    omega
  have n1 : a ≠ (65536 : BitVec 64) := ne 65536 (by omega)
  have n2 : a ≠ (65544 : BitVec 64) := ne 65544 (by omega)
  have n3 : a ≠ (65552 : BitVec 64) := ne 65552 (by omega)
  have n4 : a ≠ (65560 : BitVec 64) := ne 65560 (by omega)
  have n5 : a ≠ (65568 : BitVec 64) := ne 65568 (by omega)
  simp only [n1,n2,n3,n4,n5,if_false]

/-- Metadata writes do not alter the bitmap region function graph. -/
theorem countdownExample_bitmapGraph (bytes : List (BitVec 8)) (cbspace dataSp : Nat)
    (bitmaps : List (BitVec 64)) (rest : BitVec 64 → BitVec 64) :
    SetSep.fun2Set ((fun a => WordLocW.word (countdownExampleWords bytes cbspace dataSp bitmaps rest a)),
      fun a => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true) =
    SetSep.fun2Set ((fun a => WordLocW.word (rest a)),
      fun a => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true) := by
  funext entry
  apply propext
  simp only [SetSep.fun2Set]
  apply exists_congr
  intro a
  by_cases h : countdownExampleBitmapsDomain a = true
  · have range : 65576 ≤ a.toNat := by
      simp only [countdownExampleBitmapsDomain,decide_eq_true_eq] at h
      omega
    rw [countdownExampleWords_other bytes cbspace dataSp bitmaps rest a (Or.inr range)]
  · simp [h]

set_option maxRecDepth 4096 in
/-- All non-bitmap Stack layout facts follow from the concrete metadata. -/
theorem countdownExample_stackLayout (bytes : List (BitVec 8)) (cbspace dataSp : Nat)
    (bitmaps : List (BitVec 64)) (rest : BitVec 64 → BitVec 64)
    (bitmapLayout : SetSep.star (Misc.wordList (131072 : BitVec 64) (bitmaps.map WordLocW.word))
      (Misc.wordListExists ((131072 : BitVec 64) + 8 * BitVec.ofNat 64 bitmaps.length) dataSp)
      (SetSep.fun2Set ((fun a => WordLocW.word (rest a)),
        fun a => holByteAligned a = true ∧ countdownExampleBitmapsDomain a = true))) :
    countdownStackMemoryLayout countdownRiscVBackend countdownMachineConfig
      (countdownMachineState (countdownBytesOfWords (countdownExampleWords bytes cbspace dataSp bitmaps rest)) countdownExampleRegs)
      (countdownAsmState (countdownBytesOfWords (countdownExampleWords bytes cbspace dataSp bitmaps rest)) countdownExampleRegs)
      (fun a => WordLocW.word (countdownExampleWords bytes cbspace dataSp bitmaps rest a))
      131072 countdownExampleBitmapsDomain bytes cbspace dataSp bitmaps := by
  have init := Flapjack.Compiler.Backend.RiscVConfig.riscvPancakeInitOk countdownMachineConfig countdownMachineConfig_fields.1
  have h4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := init.2.1
  have h2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := init.2.2.2.1
  simp [countdownStackMemoryLayout,h2,h4,countdownAsmState,countdownExampleRegs,
    StackRemove.bytesInWord,countdownExampleWords,countdownMachineConfig,countdownMachineState,riscvTarget]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]
    decide
  · rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]
    decide
  · intro w _ hw
    simp only [countdownExampleBitmapsDomain, decide_eq_false_iff_not]
    change w.toNat < 131072 at hw
    omega
  · have h := bitmapLayout
    rw [← countdownExample_bitmapGraph bytes cbspace dataSp bitmaps rest] at h
    simpa [countdownExampleWords] using h

end SteppedFlapjack.PanToCrepSteps
