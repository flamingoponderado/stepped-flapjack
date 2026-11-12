import SteppedFlapjack.Concrete.InitEStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.LoopToWordSteps

namespace SteppedFlapjack.Concrete

/-- The initialized Stack heap starts at the fixture base and preserves Lab memory. -/
theorem configuredStack_heapBaseAndMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (configuredStack code cfg bs).store.lookup .currHeap = some (.word heapBase) ∧
      ∀ a, (configuredStack code cfg bs).mdomain a = true → (configuredStack code cfg bs).memory a = configuredLabMemory code bs a := by
  let ctx := configuredStackContext code cfg bs fits good
  obtain ⟨current,read,store,mem⟩ := ctx.heap_base_and_memory_lab
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have eq : current = heapBase := by
    simpa [ctx,configuredStackContext,configuredLab,fixtureLab,r2,fixtureLabRegs,eq_comm] using read
  subst current
  exact ⟨store,mem⟩

/-- The initialized half-heap length matches the source fixture. -/
theorem configuredStack_heapLength (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (configuredStack code cfg bs).store.lookup .heapLength = some (.word fixtureHeapLength) := by
  let ctx := configuredStackContext code cfg bs fits good
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have r3 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3 = 12 := by with_unfolding_all rfl
  have r4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := by with_unfolding_all rfl
  have length := ctx.heap_length_lab
  simp only [FullInitStackContext.labHeapLength,ctx,configuredStackContext,r2,r3,r4] at length
  change (configuredStack code cfg bs).store.lookup .heapLength = some (.word (BitVec.ofNat 64 (Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits.getStackHeapLimit (2^53-1) (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd)).2 * StackRemove.bytesInWord 64)) at length
  rw [fixture_init_limits] at length
  simpa [fixtureHeapLength,StackRemove.bytesInWord] using length
/-- The initialized Stack heap domain is exactly the source domain. -/
theorem configuredStack_heapDomain (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (a : BitVec 64) :
    (configuredStack code cfg bs).mdomain a = true ↔ ordinaryAddress a := by
  let ctx := configuredStackContext code cfg bs fits good
  have current := (configuredStack_heapBaseAndMemory code cfg bs fits good).1
  have hlen := ctx.heap_length_lab
  have concrete := configuredStack_heapLength code cfg bs fits good
  have lenEq : ctx.labHeapLength = fixtureHeapLength := by
    rw [concrete] at hlen
    exact WordLocW.word.inj (Option.some.inj hlen).symm
  have other := ctx.heap_end_lab heapBase current
  rw [lenEq] at other
  have domain := ctx.heap_domain_of_pointers heapBase (heapBase+fixtureHeapLength) current other a
  rw [domain,ordinaryAddress_eq_addresses]
  have count : ((heapBase+fixtureHeapLength-heapBase).toNat / 8) +
      ((heapBase+fixtureHeapLength-heapBase).toNat / 8) = (stackStart-sourceBase)/8-globalsWords-1 := by decide
  rw [count]
/-- Stack memory agrees with the source on every accessible heap word. -/
theorem configuredStack_heapMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (a : BitVec 64)
    (member : ordinaryAddress a) : (configuredStack code cfg bs).memory a = .word (initialWordFor bs.length a) := by
  have domain := (configuredStack_heapDomain code cfg bs fits good a).2 member
  have eq := (configuredStack_heapBaseAndMemory code cfg bs fits good).2 a domain
  have heap : sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0 := by
    refine ⟨member.1,?_,member.2.2⟩
    simp only [ordinaryAddress,fixtureHeapEnd,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords] at member ⊢
    omega
  have read := configuredLab_heapRead code cfg bs fits a heap
  change configuredLabMemory code bs a = .word (initialWordFor bs.length a) at read
  exact eq.trans read

/-- Initialized Stack memory agrees with the source on its accessible domain. -/
theorem configuredStack_sourceMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    crepToLoopMemRelHOLExact (sourceTemplateFor bs.length).memory (configuredStack code cfg bs).memory
      (sourceTemplateFor bs.length).memaddrs := by
  intro address member
  change wlabWlocExact (.word (initialWordFor bs.length address)) = (configuredStack code cfg bs).memory address
  exact (configuredStack_heapMemory code cfg bs fits good address member).symm

/-- The FFI, byte order and shared-memory domain match the source fixture. -/
theorem configuredStack_ambient (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (configuredStack code cfg bs).ffi = sourceFfi ∧ (configuredStack code cfg bs).be = false ∧
      (configuredStack code cfg bs).shMdomain = (fun a => decide (sharedAddress a)) := by
  let ctx := configuredStackContext code cfg bs fits good
  have ffi := ctx.ffi_eq
  have ambient := ctx.ambient_eq
  exact ⟨by simpa [ctx,configuredStackContext,configuredLab,fixtureLab] using ffi,
    by simpa [ctx,configuredStackContext,configuredLab,fixtureLab] using ambient.2.1,
    by simpa [ctx,configuredStackContext,configuredLab,fixtureLab] using ambient.2.2⟩

theorem fixtureStack_heapMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (a : BitVec 64)
    (member : ordinaryAddress a) : (fixtureStack code cfg).memory a = .word (initialWord a) := by
  have fits : 0xa0020018 + ([4] : List (BitVec 64)).length*8 ≤ sourceBase := by decide
  have h := configuredStack_heapMemory code cfg [4] fits good a member
  rw [configuredStack_one] at h
  simpa [initialWordFor_one] using h

end SteppedFlapjack.Concrete
