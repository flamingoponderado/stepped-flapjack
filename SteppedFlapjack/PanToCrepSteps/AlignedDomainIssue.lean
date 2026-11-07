import SteppedFlapjack.PanToCrepSteps.CountdownMachineState
import SteppedFlapjack.PanToCrepSteps.CountdownStackInit
import SteppedFlapjack.LoopToWordSteps.FullInitNativeValidity

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

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.StackRemove

theorem stackAssumptions_domain_nonempty {C F : Type} (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
 (offset : BitVec 64 × BitVec 64) (bm : List (BitVec 64)) (code : List (Nat × HolProg 64))
 (t : LabSem.State 64 C F) (save : Nat → Bool) (ds : Nat)
 (oracle : Nat → C × List (Nat × HolProg 64) × List (BitVec 64))
 (h : Assumptions sc dc mh sp offset bm code t save ds oracle) : ∃ a, t.memDomain a = true := by
  have mem := h.2.2.2.2.1
  obtain ⟨p2,p3,p4,bp,_,_,_,_,_,_,_,_,_,_,_,_,_,space,sep⟩ := mem
  have positive : 0 < ((-1 * p2 + p4).toNat / (StackRemove.bytesInWord 64).toNat) := by
    have bound := space
    change (8192 : BitVec 64) ≤ p4 - p2 at bound
    have boundNat : 8192 ≤ (p4-p2).toNat := by exact bound
    have eq : -1 * p2 + p4 = p4-p2 := by
      have neg : (-1 : BitVec 64) * p2 = -p2 := (BitVec.neg_eq_neg_one_mul p2).symm
      rw [neg,BitVec.add_comm,← BitVec.sub_eq_add_neg]
    rw [eq]
    change 0 < (p4-p2).toNat / 8
    omega
  rcases sep with ⟨left,right,⟨union,_⟩,_,hexists⟩
  rcases hexists with ⟨values,assertion⟩
  obtain ⟨listHeap,len⟩ := (WordListExists.starCond _ _ _).mp assertion
  have lenPos : 0 < values.length := by omega
  have member := StackHeap.wordListNth p2 values right 0 lenPos listHeap
  have graph : SetSep.fun2Set (t.memory, fun a => t.memDomain a = true) (p2,values[0]) := by
    rw [← union]
    apply Or.inr
    simpa using member
  exact ⟨p2,((SetSep.fun2SetThm _ _ _ _).mp graph).2⟩

theorem stackAssumptions_closed_incompatible {C F : Type} (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
 (offset : BitVec 64 × BitVec 64) (bm : List (BitVec 64)) (code : List (Nat × HolProg 64))
 (t : LabSem.State 64 C F) (save : Nat → Bool) (ds : Nat)
 (oracle : Nat → C × List (Nat × HolProg 64) × List (BitVec 64))
 (h : Assumptions sc dc mh sp offset bm code t save ds oracle)
 (closed : ∀ a, t.memDomain (holByteAlign a) = true → t.memDomain a = true) : False := by
  have aligned : ∀ a, t.memDomain a = true → holByteAligned a = true := by
    intro a ha
    have hh := h.2.2.2.2.2.2.2.2.2.2.1 a ha
    have log : holLOG2 8 = 3 := by rw [holLOG2_eq_log2 (by decide)]; decide
    simpa only [holByteAligned,Nat.reduceDiv,log] using (holAligned_iff 3 a).mpr hh
  have hc : ∀ a, (t.memDomain (holByteAlign a) && holByteAligned (holByteAlign a)) = true →
      (t.memDomain a && holByteAligned a) = true := by
    intro a hpre
    have domain : t.memDomain (holByteAlign a) = true := by
      cases hd : t.memDomain (holByteAlign a) <;> simp_all
    have domain' := closed a domain
    simp [domain',aligned a domain']
  obtain ⟨a,ha⟩ := stackAssumptions_domain_nonempty sc dc mh sp offset bm code t save ds oracle h
  have empty := alignedDomain_closed_empty t.memDomain hc a
  rw [ha,aligned a ha] at empty
  contradiction

open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
theorem unalignedLabInit_incompatible {F : Type} (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
 (offset : BitVec 64 × BitVec 64) (bm : List (BitVec 64)) (code : List (Nat × HolProg 64))
 (save : Nat → Bool) (ds : Nat) (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
 (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (ms : RiscV.L3.riscv_state)
 (ffi : HolFfiState F) (asm : AsmState 64) (mem : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool)
 (labCode : LabSem.LabProgHOL 64) (comp : LabToTarget.Config → LabSem.LabProgHOL 64 → Option (List (BitVec 8) × LabToTarget.Config))
 (pos : BitVec 64) (cb : Nat) (labOracle : Nat → LabToTarget.Config × LabSem.LabProgHOL 64) (bytes : List (BitVec 8))
 (h : Assumptions sc dc mh sp offset bm code (LabToTarget.makeInit mc ffi asm mem dm sdm ms labCode comp pos cb labOracle) save ds oracle)
 (init : goodInitState mc ms bytes cb asm mem dm sdm) : False := by
  apply stackAssumptions_closed_incompatible sc dc mh sp offset bm code _ save ds oracle h
  simpa only [LabToTarget.makeInit] using init.2.2.2.2.2.2.2.2.2.2.2.1

end SteppedFlapjack.PanToCrepSteps
