import SteppedFlapjack.Concrete.InitEStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.LoopToWordSteps

namespace SteppedFlapjack.Concrete

/-- The initialized Stack heap starts at the fixture base and preserves Lab memory. -/
theorem fixtureStack_heapBaseAndMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (fixtureStack code cfg).store.lookup .currHeap = some (.word heapBase) ∧
      ∀ a, (fixtureStack code cfg).mdomain a = true → (fixtureStack code cfg).memory a = fixtureLabMemoryFor code a := by
  let ctx := fixtureStackContext code cfg good
  obtain ⟨current,read,store,mem⟩ := ctx.heap_base_and_memory_lab
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have eq : current = heapBase := by
    simpa [ctx,fixtureStackContext,fixtureLab,r2,fixtureLabRegs,eq_comm] using read
  subst current
  exact ⟨store,mem⟩

/-- The initialized half-heap length matches the source fixture. -/
theorem fixtureStack_heapLength (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (fixtureStack code cfg).store.lookup .heapLength = some (.word fixtureHeapLength) := by
  let ctx := fixtureStackContext code cfg good
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have r3 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3 = 12 := by with_unfolding_all rfl
  have r4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := by with_unfolding_all rfl
  have length := ctx.heap_length_lab
  simp only [FullInitStackContext.labHeapLength,ctx,fixtureStackContext,fixtureLab,r2,r3,r4,fixtureLabRegs] at length
  simp only [show (12 : Nat) ≠ 11 by decide,show (13 : Nat) ≠ 11 by decide,show (13 : Nat) ≠ 12 by decide,if_false,if_true,wordSemTheWord] at length
  change (fixtureStack code cfg).store.lookup .heapLength = some (.word (BitVec.ofNat 64 (Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits.getStackHeapLimit (2^53-1) (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd)).2 * StackRemove.bytesInWord 64)) at length
  rw [fixture_init_limits] at length
  simpa [fixtureHeapLength,StackRemove.bytesInWord] using length
/-- The initialized Stack heap domain is exactly the source domain. -/
theorem fixtureStack_heapDomain (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (a : BitVec 64) :
    (fixtureStack code cfg).mdomain a = true ↔ ordinaryAddress a := by
  let ctx := fixtureStackContext code cfg good
  have current := (fixtureStack_heapBaseAndMemory code cfg good).1
  have hlen := ctx.heap_length_lab
  have concrete := fixtureStack_heapLength code cfg good
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
theorem fixtureStack_heapMemory (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (a : BitVec 64)
    (member : ordinaryAddress a) : (fixtureStack code cfg).memory a = .word (initialWord a) := by
  have domain := (fixtureStack_heapDomain code cfg good a).2 member
  have eq := (fixtureStack_heapBaseAndMemory code cfg good).2 a domain
  have ne : a ≠ fixtureBitmapBase := by
    intro h
    subst a
    simp [ordinaryAddress,fixtureBitmapBase,sourceBase] at member
  have labDomain : fixtureLabDomain a := Or.inr ⟨member.1, by
    simp only [ordinaryAddress,fixtureHeapEnd,heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords] at member ⊢
    omega, member.2.2⟩
  simpa [fixtureLabMemoryFor,labDomain,fixtureLabMemory,ne] using eq

/-- The FFI, byte order and shared-memory domain match the source fixture. -/
theorem fixtureStack_ambient (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (fixtureStack code cfg).ffi = sourceFfi ∧ (fixtureStack code cfg).be = false ∧
      (fixtureStack code cfg).shMdomain = (fun a => decide (sharedAddress a)) := by
  let ctx := fixtureStackContext code cfg good
  have ffi := ctx.ffi_eq
  have ambient := ctx.ambient_eq
  exact ⟨by simpa [ctx,fixtureStackContext,fixtureLab] using ffi,
    by simpa [ctx,fixtureStackContext,fixtureLab] using ambient.2.1,
    by simpa [ctx,fixtureStackContext,fixtureLab] using ambient.2.2⟩

end SteppedFlapjack.Concrete
