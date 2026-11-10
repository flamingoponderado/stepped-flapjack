import SteppedFlapjack.Concrete.InitELab
import SteppedFlapjack.LabToTargetSteps.ByteClosure
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig

/-! Byte-closed machine domains corresponding to the init-e-shaped fixture. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LabToTargetSteps

/-- The word-addressed fixture heap and bitmap are aligned. -/
theorem fixtureLabDomain_aligned (a : BitVec 64) (h : fixtureLabDomain a) : holByteAligned a = true := by
  rcases h with h | h
  · subst a
    rw [holByteAligned_iff_mod (Or.inr rfl)]
    decide
  · rw [holByteAligned_iff_mod (Or.inr rfl)]
    exact h.2.2

/-- Machine data memory contains all bytes of each fixture word. -/
noncomputable def fixtureByteDomain : BitVec 64 → Bool :=
  byteClosure (fun a => decide (fixtureLabDomain a))

/-- Machine shared memory contains all bytes of each fixture shared word. -/
noncomputable def fixtureSharedByteDomain : BitVec 64 → Bool :=
  byteClosure (fun a => decide (sharedAddress a))

theorem fixtureByteDomain_closed (a : BitVec 64) :
    fixtureByteDomain (holByteAlign a) = true → fixtureByteDomain a = true :=
  byteClosure_closed _ a

theorem fixtureSharedByteDomain_closed (a : BitVec 64) :
    fixtureSharedByteDomain (holByteAlign a) = true → fixtureSharedByteDomain a = true :=
  byteClosure_closed _ a

/-- Aligning the machine data domain recovers the Lab fixture's word domain. -/
theorem fixtureByteDomain_aligned :
    (fun a => fixtureByteDomain a && holByteAligned a) = fun a => decide (fixtureLabDomain a) := by
  apply byteClosure_aligned
  intro a h
  exact fixtureLabDomain_aligned a (of_decide_eq_true h)

/-- Aligning the machine shared domain recovers the source shared-word domain. -/
theorem fixtureSharedByteDomain_aligned :
    (fun a => fixtureSharedByteDomain a && holByteAligned a) = fun a => decide (sharedAddress a) := by
  apply byteClosure_aligned
  intro a h
  exact (sharedAddress_alignment a).1 (of_decide_eq_true h) |>.1

/-- The machine code/data and shared domains are disjoint by construction. -/
noncomputable def fixtureMachineConfig (pc : BitVec 64) : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection :=
  { countdownMachineConfig with
    progAddresses := fun a => pc.toNat ≤ a.toNat ∧ fixtureSharedByteDomain a = false
    sharedAddresses := fun a => fixtureSharedByteDomain a = true
    haltPc := pc - 16
    ccachePc := pc - 32 }

theorem fixtureMachineConfig_disjoint (pc : BitVec 64) :
    Disjoint (α := Set (BitVec 64)) (Set.ofPred (fixtureMachineConfig pc).progAddresses)
      (Set.ofPred (fixtureMachineConfig pc).sharedAddresses) := by
  simp [fixtureMachineConfig,Set.disjoint_left]


/-- All fixture data bytes lie in program memory when code starts below the bitmap. -/
theorem fixtureByteDomain_in_program (pc a : BitVec 64)
    (pcBound : pc.toNat ≤ 0xa0020018) (inData : fixtureByteDomain a = true) :
    (fixtureMachineConfig pc).progAddresses a := by
  have data : fixtureLabDomain (holByteAlign a) := by
    simpa [fixtureByteDomain,byteClosure] using inData
  have base : 0xa0020018 ≤ (holByteAlign a).toNat := by
    rcases data with h | h
    · rw [h]
      decide
    · simp only [sourceBase] at h
      omega
  have alignedLe : (holByteAlign a).toNat ≤ a.toNat := by
    rw [holByteAlign_toNat (Or.inr rfl)]
    exact Nat.div_mul_le_self _ _
  have notShared : fixtureSharedByteDomain a = false := by
    cases h : fixtureSharedByteDomain a with
    | false => rfl
    | true =>
      have shared : sharedAddress (holByteAlign a) := by
        simpa [fixtureSharedByteDomain,byteClosure] using h
      simp only [sharedAddress,inputStart,inputEnd,inputSize,outputStart,outputEnd,outputSize] at shared
      rcases data with bitmap | heap
      · rw [bitmap] at shared
        simp [fixtureBitmapBase] at shared
      · simp only [sourceBase] at heap
        omega
  exact ⟨by omega,notShared⟩


/-- The code and service-address region is outside the init-e shared ranges. -/
theorem fixtureSharedByteDomain_false_between (a : BitVec 64)
    (lo : 0x80000000 ≤ a.toNat) (hi : a.toNat < 0xa0410000) :
    fixtureSharedByteDomain a = false := by
  cases h : fixtureSharedByteDomain a with
  | false => rfl
  | true =>
    have shared : sharedAddress (holByteAlign a) := by
      simpa [fixtureSharedByteDomain,byteClosure] using h
    simp only [sharedAddress,inputStart,inputEnd,inputSize,outputStart,outputEnd,outputSize] at shared
    rw [holByteAlign_toNat (Or.inr rfl)] at shared
    omega

/-- The concrete service addresses satisfy the target's start-PC contract. -/
theorem fixtureMachineConfig_startPc (pc : BitVec 64)
    (lo : 0x80000020 ≤ pc.toNat) (hi : pc.toNat < 0xa0410000)
    (aligned : (1 &&& pc) = 0) : startPcOk (fixtureMachineConfig pc) pc := by
  have less16 : (16 : BitVec 64) ≤ pc := by rw [BitVec.le_def]; change 16 ≤ pc.toNat; omega
  have less32 : (32 : BitVec 64) ≤ pc := by rw [BitVec.le_def]; change 32 ≤ pc.toNat; omega
  have sub16 : (pc - 16).toNat = pc.toNat - 16 := by rw [BitVec.toNat_sub_of_le less16]; rfl
  have sub32 : (pc - 32).toNat = pc.toNat - 32 := by rw [BitVec.toNat_sub_of_le less32]; rfl
  have noShared16 : fixtureSharedByteDomain (pc - 16) = false :=
    fixtureSharedByteDomain_false_between _ (by rw [sub16]; omega) (by rw [sub16]; omega)
  have noShared32 : fixtureSharedByteDomain (pc - 32) = false :=
    fixtureSharedByteDomain_false_between _ (by rw [sub32]; omega) (by rw [sub32]; omega)
  have index : mmioPcsMinIndex [] = some 0 := by
    apply mmioPcsMinIndex_eq_some
    simp [mmioIndexBoundary]
  refine ⟨?_,?_,?_,?_,?_,?_,aligned,0,?_,?_,?_,?_⟩
  · change ¬ (pc.toNat ≤ (pc - 16).toNat ∧ _)
    rw [sub16]
    omega
  · change ¬ (pc.toNat ≤ (pc - 32).toNat ∧ _)
    rw [sub32]
    omega
  · change ¬ fixtureSharedByteDomain (pc - 16) = true
    intro h
    rw [noShared16] at h
    contradiction
  · change ¬ fixtureSharedByteDomain (pc - 32) = true
    intro h
    rw [noShared32] at h
    contradiction
  · rfl
  · rfl
  · exact index
  · simp
  · simp [fixtureMachineConfig,countdownMachineConfig]
  · rfl


/-- Addresses below the bitmap cannot belong to the fixture data domain. -/
theorem fixtureByteDomain_false_below (a : BitVec 64) (below : a.toNat < 0xa0020018) :
    fixtureByteDomain a = false := by
  cases h : fixtureByteDomain a with
  | false => rfl
  | true =>
    have data : fixtureLabDomain (holByteAlign a) := by
      simpa [fixtureByteDomain,byteClosure] using h
    have alignedLe : (holByteAlign a).toNat ≤ a.toNat := by
      rw [holByteAlign_toNat (Or.inr rfl)]
      exact Nat.div_mul_le_self _ _
    rcases data with bitmap | heap
    · rw [bitmap] at alignedLe
      have v : fixtureBitmapBase.toNat = 0xa0020018 := rfl
      rw [v] at alignedLe
      omega
    · simp only [sourceBase] at heap
      omega


/-- The fixture machine has identity ordinary interference and no FFI entries. -/
theorem fixtureMachineConfig_interference (pc : BitVec 64) :
    interferenceOk (fixtureMachineConfig pc).nextInterfer
      ((fixtureMachineConfig pc).target.proj (fixtureMachineConfig pc).progAddresses) ∧
    ∀ start, ffiInterferOkHOL start (fixtureMachineConfig pc) := by
  constructor
  · intro i state
    rfl
  · intro start state k index newBytes asm bytes bytes2 i h
    simp [fixtureMachineConfig,countdownMachineConfig] at h

set_option maxRecDepth 4096 in
/-- The fixture cache-flush service preserves memory and registers. -/
theorem fixtureMachineConfig_ccache (pc start : BitVec 64) :
    ccacheInterferOkHOL start (fixtureMachineConfig pc) := by
  intro state asm k a1 a2 ⟨rel,aligned⟩
  have ok : riscvOk state = true := rel.1
  have regs := rel.2.2.2.1
  have link : state.c_gpr state.procID 1 = asm.regs 1 := by
    have h := regs 1 (by
      change 1 < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains 1 = false
      decide)
    exact h
  have valid := (riscvOk_iff state).mp ok
  refine ⟨?_,?_,?_,?_⟩
  · apply (riscvOk_iff _).mpr
    refine ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,?_⟩
    simp only [fixtureMachineConfig,countdownMachineConfig]
    rw [link]
    exact aligned
  · simpa [fixtureMachineConfig,countdownMachineConfig,riscvTarget,riscvConfig] using link
  · intro a ha
    exact rel.2.2.1 a ha
  · intro r hr
    exact regs r ⟨hr.2.1,by simpa using hr.2.2⟩

end SteppedFlapjack.Concrete
