import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import SteppedFlapjack.PanToCrepSteps.CountdownStackInit

/-! Check the interaction of the byte-domain and word-domain initializer premises. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- A byte-closed domain containing only word-aligned addresses is empty. -/
theorem alignedDomain_closed_empty (base : BitVec 64 → Bool)
    (closed : ∀ a, (base (holByteAlign a) && holByteAligned (holByteAlign a)) = true →
      (base a && holByteAligned a) = true) :
    ∀ a, (base a && holByteAligned a) = false := by
  intro a
  cases ha : base a && holByteAligned a with
  | false => rfl
  | true =>
    have aligned : holByteAligned a = true := by
      cases h : holByteAligned a <;> simp_all
    have log : holLOG2 8 = 3 := by
      rw [holLOG2_eq_log2 (by decide)]
      decide
    have aligned3 : holAligned 3 a = true := by
      simpa only [holByteAligned,Nat.reduceDiv,log] using aligned
    have mod0 : a.toNat % 8 = 0 := by
      simpa using (holAligned_iff 3 a).mp aligned3
    have room : a.toNat + 1 < 2^64 := by
      have bound := a.isLt
      omega
    have sumNat : (a+1).toNat = a.toNat+1 := by
      rw [BitVec.toNat_add]
      change (a.toNat+1) % (2^64) = a.toNat+1
      rw [Nat.mod_eq_of_lt room]
    have halign : holByteAlign (a+1) = a := by
      apply BitVec.eq_of_toNat_eq
      simp only [holByteAlign,Nat.reduceDiv,log,holAlign_eq_div,BitVec.toNat_ofNat,sumNat]
      have bound : ((a.toNat+1)/8)*8 < 2^64 := by
        have h := Nat.div_mul_le_self (a.toNat+1) 8
        omega
      rw [Nat.mod_eq_of_lt bound]
      omega
    have hnot : holByteAligned (a+1) = false := by
      have one : holAligned 3 (1 : BitVec 64) = false := by
        cases h : holAligned 3 (1 : BitVec 64) with
        | false => rfl
        | true =>
          have impossible := (holAligned_iff 3 (1 : BitVec 64)).mp h
          change 1 % 8 = 0 at impossible
          omega
      have h := (alignedAddSub 3 (1 : BitVec 64) a aligned3).1
      have h' : holAligned 3 (a+1) = false := by
        rw [BitVec.add_comm]
        exact h.trans one
      simpa only [holByteAligned,Nat.reduceDiv,log] using h'
    have next := closed (a+1)
    rw [halign,ha] at next
    have bad := next rfl
    rw [hnot,Bool.and_false] at bad
    contradiction

/-- The current aligned countdown domain conflicts with byte-closure when the
Stack layout supplies a nonempty heap. This exposes a missing alignment bridge. -/
theorem countdown_alignedDomain_incompatible
    (config : Backend.Config) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (machine : RiscV.L3.riscv_state) (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64)
    (bitmapPtr : BitVec 64) (bitmapsDomain : BitVec 64 → Bool) (bytes : List (BitVec 8))
    (cbspace dataSp : Nat) (bitmaps : List (BitVec 64))
    (layout : countdownStackMemoryLayout config mc machine asm memory bitmapPtr bitmapsDomain bytes cbspace dataSp bitmaps)
    (closed : ∀ a, countdownStackLabDomain config asm bitmapsDomain (holByteAlign a) = true →
      countdownStackLabDomain config asm bitmapsDomain a = true) : False := by
  let lo := asm.regs (StackNames.findNameSpt config.stackConf.regNames 2)
  let hi := asm.regs (StackNames.findNameSpt config.stackConf.regNames 4)
  have aligned : holByteAligned lo = true := layout.1
  have order : lo ≤ hi := layout.2.2.2.1
  have enough : (8192 : BitVec 64) ≤ hi - lo := by
    simpa [lo,hi,StackRemove.bytesInWord] using layout.2.2.2.2.1
  have strict : lo < hi := by
    have ne : lo ≠ hi := by
      intro eq
      rw [← eq,BitVec.sub_self] at enough
      contradiction
    change lo.toNat < hi.toNat
    change lo.toNat ≤ hi.toNat at order
    have neNat : lo.toNat ≠ hi.toNat := by
      intro h
      exact ne (BitVec.eq_of_toNat_eq h)
    omega
  let raw : BitVec 64 → Bool := fun a => decide (lo ≤ a ∧ a < hi) || bitmapsDomain a
  have witness : (raw lo && holByteAligned lo) = true := by
    simp [raw,strict,aligned]
  have empty := alignedDomain_closed_empty raw (by simpa [raw,lo,hi,countdownStackLabDomain] using closed) lo
  rw [witness] at empty
  contradiction

/-- The current combined countdown theorem's initializer and Stack layout
premises cannot both hold. A byte-domain to aligned-domain bridge is required. -/
theorem countdown_goodInit_layout_incompatible
    (config : Backend.Config) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (machine : RiscV.L3.riscv_state) (asm : AsmState 64) (memory : BitVec 64 → WordLocW 64)
    (bitmapPtr : BitVec 64) (bitmapsDomain sharedDomain : BitVec 64 → Bool) (bytes : List (BitVec 8))
    (cbspace dataSp : Nat) (bitmaps : List (BitVec 64))
    (layout : countdownStackMemoryLayout config mc machine asm memory bitmapPtr bitmapsDomain bytes cbspace dataSp bitmaps)
    (init : goodInitState mc machine bytes cbspace asm memory (countdownStackLabDomain config asm bitmapsDomain)
      (fun a => sharedDomain a && holByteAligned a)) : False := by
  exact countdown_alignedDomain_incompatible config mc machine asm memory bitmapPtr bitmapsDomain bytes cbspace dataSp bitmaps
    layout init.2.2.2.2.2.2.2.2.2.2.2.1

end SteppedFlapjack.PanToCrepSteps
