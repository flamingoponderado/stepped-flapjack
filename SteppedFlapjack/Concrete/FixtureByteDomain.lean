import SteppedFlapjack.Concrete.InitELab
import SteppedFlapjack.LabToTargetSteps.ByteClosure
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig

/-! Byte-closed machine domains corresponding to the init-e-shaped fixture. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.Proofs.PanToTarget
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LabToTargetSteps

/-- Machine byte domain for all compiler-provided bitmaps and the source heap. -/
noncomputable def configuredByteDomain (bs : List (BitVec 64)) : BitVec 64 → Bool :=
  byteClosure (fun a => decide (configuredLabDomain bs a))

theorem configuredLabDomain_aligned (bs : List (BitVec 64)) (a : BitVec 64)
    (h : configuredLabDomain bs a) : holByteAligned a = true := by
  rw [holByteAligned_iff_mod (Or.inr rfl)]
  rcases h with bitmap | heap
  · exact bitmap.2.2
  · exact heap.2.2

theorem configuredByteDomain_closed (bs : List (BitVec 64)) (a : BitVec 64) :
    configuredByteDomain bs (holByteAlign a) = true → configuredByteDomain bs a = true :=
  byteClosure_closed _ a

theorem configuredByteDomain_aligned (bs : List (BitVec 64)) :
    (fun a => configuredByteDomain bs a && holByteAligned a) = fun a => decide (configuredLabDomain bs a) := by
  apply byteClosure_aligned
  intro a h
  exact configuredLabDomain_aligned bs a (of_decide_eq_true h)

theorem configuredByteDomain_false_below (bs : List (BitVec 64)) (a : BitVec 64)
    (below : a.toNat < 0xa0020018) : configuredByteDomain bs a = false := by
  cases h : configuredByteDomain bs a with
  | false => rfl
  | true =>
    have data : configuredLabDomain bs (holByteAlign a) := by
      simpa [configuredByteDomain,byteClosure] using h
    have alignedLe : (holByteAlign a).toNat ≤ a.toNat := by
      rw [holByteAlign_toNat (Or.inr rfl)]
      exact Nat.div_mul_le_self _ _
    rcases data with bitmap | heap
    · simp only [bitmapDomain] at bitmap
      omega
    · simp only [sourceBase] at heap
      omega

/-- Machine data memory contains all bytes of each fixture word. -/
noncomputable def fixtureByteDomain : BitVec 64 → Bool :=
  byteClosure (fun a => decide (fixtureLabDomain a))

theorem configuredLabDomain_one (a : BitVec 64) : configuredLabDomain [4] a ↔ fixtureLabDomain a := by
  simp [configuredLabDomain, fixtureLabDomain, bitmapDomain_singleton]

theorem configuredByteDomain_one : configuredByteDomain [4] = fixtureByteDomain := by
  unfold configuredByteDomain fixtureByteDomain
  congr 1
  funext a
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using configuredLabDomain_one a

/-- The word-addressed fixture heap and bitmap are aligned. -/
theorem fixtureLabDomain_aligned (a : BitVec 64) (h : fixtureLabDomain a) : holByteAligned a = true := by
  apply configuredLabDomain_aligned [4] a
  simpa [configuredLabDomain, fixtureLabDomain, bitmapDomain_singleton] using h

/-- Machine shared memory contains all bytes of each fixture shared word. -/
noncomputable def fixtureSharedByteDomain : BitVec 64 → Bool :=
  byteClosure (fun a => decide (sharedAddress a))

theorem fixtureSharedByteDomain_closed (a : BitVec 64) :
    fixtureSharedByteDomain (holByteAlign a) = true → fixtureSharedByteDomain a = true :=
  byteClosure_closed _ a

/-- Aligning the machine data domain recovers the Lab fixture's word domain. -/
theorem fixtureByteDomain_aligned :
    (fun a => fixtureByteDomain a && holByteAligned a) = fun a => decide (fixtureLabDomain a) := by
  have h := configuredByteDomain_aligned [4]
  rw [configuredByteDomain_one] at h
  have domains : (fun a => decide (configuredLabDomain [4] a)) =
      (fun a => decide (fixtureLabDomain a)) := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using configuredLabDomain_one a
  rw [domains] at h
  exact h

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


/-- The bitmap must end before the init-e shared output region. -/
theorem configuredByteDomain_in_program (bs : List (BitVec 64)) (pc a : BitVec 64)
    (bitmapFits : 0xa0020018 + bs.length * 8 ≤ 0xa0410000)
    (pcBound : pc.toNat ≤ 0xa0020018) (inData : configuredByteDomain bs a = true) :
    (fixtureMachineConfig pc).progAddresses a := by
  have data : configuredLabDomain bs (holByteAlign a) := by
    simpa [configuredByteDomain,byteClosure] using inData
  have alignedLe : (holByteAlign a).toNat ≤ a.toNat := by
    rw [holByteAlign_toNat (Or.inr rfl)]
    exact Nat.div_mul_le_self _ _
  have base : 0xa0020018 ≤ (holByteAlign a).toNat := by
    rcases data with bitmap | heap
    · exact bitmap.1
    · simp only [sourceBase] at heap
      omega
  have notShared : fixtureSharedByteDomain a = false := by
    cases h : fixtureSharedByteDomain a with
    | false => rfl
    | true =>
      have shared : sharedAddress (holByteAlign a) := by
        simpa [fixtureSharedByteDomain,byteClosure] using h
      simp only [sharedAddress,inputStart,inputEnd,inputSize,outputStart,outputEnd,outputSize] at shared
      rcases data with bitmap | heap
      · simp only [bitmapDomain] at bitmap
        omega
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
