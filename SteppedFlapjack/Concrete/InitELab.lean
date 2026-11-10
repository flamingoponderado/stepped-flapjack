import SteppedFlapjack.Concrete.InitEMemory
import Flapjack.Compiler.Backend.RiscVConfig.Proofs
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.RiscVConfig

namespace SteppedFlapjack.Concrete

/-- Concrete heap and stack pointer registers for the Lab initializer. -/
def fixtureLabRegs (r : Nat) : WordLocW 64 :=
  if r = 11 then .word heapBase else if r = 12 then .word (BitVec.ofNat 64 heapEnd)
  else if r = 13 then .word (BitVec.ofNat 64 ramEnd) else .word 0

/-- The init-e-shaped Lab state for an arbitrary native Stack code table. -/
noncomputable def fixtureLab (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) : LabSem.State 64 LabToTarget.Config Unit where
  regs := fixtureLabRegs
  fpRegs := fun _ => 0
  memory := fixtureLabMemory
  memDomain := fun a => decide (fixtureLabDomain a)
  sharedMemDomain := fun a => decide (sharedAddress a)
  pc := 0
  be := false
  ffi := sourceFfi
  ioRegs := fun _ _ _ => none
  ccRegs := fun _ _ => none
  ioFpRegs := fun _ _ => 0
  ccFpRegs := fun _ _ => 0
  code := StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset code
  compile := fun _ _ => none
  compileOracle := fun _ => (cfg,StackToLab.compileNoStubs countdownRiscVBackend.stackConf.regNames countdownRiscVBackend.stackConf.jump riscvConfig.addrOffset 24 [])
  codeBuffer := ⟨0x800f0134,[],0xecc⟩
  clock := 0
  failed := false
  ptrReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 1
  lenReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2
  ptr2Reg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3
  len2Reg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4
  linkReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete Lab state meets the full initializer memory contract. -/
theorem fixtureLab_memoryAssumption (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    StackToLab.Proofs.MakeInit.memoryAssumption countdownRiscVBackend.stackConf.regNames [4] 0 (fixtureLab code cfg) := by
  refine ⟨heapBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd,fixtureBitmapBase,?_⟩
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have r3 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3 = 12 := by with_unfolding_all rfl
  have r4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := by with_unfolding_all rfl
  have heapCount : ((-1 * heapBase + BitVec.ofNat 64 ramEnd).toNat / (StackRemove.bytesInWord 64).toNat) = fixtureLabHeapWords := by decide
  have bitmapEnd : fixtureBitmapBase + StackRemove.bytesInWord 64 * BitVec.ofNat 64 (([4] : List (BitVec 64)).length) = fixtureBitmapBase+8 := by decide
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at bitmapEnd
  have sep := fixtureLabMemory_separated
  simp only [fixtureLab,r2,r3,r4,fixtureLabRegs] 
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by trivial,
    by decide,by rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide,
    by rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide,
    by rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide,by decide,?_⟩
  simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,bitmapEnd,heapCount,decide_eq_true_eq] using sep

/-- Saved Lab registers used by the concrete initializer. -/
noncomputable def fixtureSavedRegs (r : Nat) : Bool := decide (r = StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 24 ∨
  r = StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 25 ∨
  r = StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 26)

/-- A no-install oracle for the finite scalar witnesses. -/
def fixtureStackOracle (cfg : LabToTarget.Config) : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64) :=
  fun _ => (cfg,[],[])

/-- The RISC-V register renaming is a bijection. -/
theorem fixtureRegNames_bijective : Function.Bijective (StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames) := by
  have hfun : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames =
      Flapjack.RiscV.riscvRegisterName := by
    funext r
    exact riscvNames_lookup_eq r
  rw [hfun]
  constructor
  · intro a b h
    by_cases ha : a < 32 <;> by_cases hb : b < 32
    · exact Flapjack.RiscV.riscvRegisterName_injective_lt_32 ha hb h
    · have := Flapjack.RiscV.riscvRegisterName_lt_32 ha
      rw [h, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at this
      omega
    · have := Flapjack.RiscV.riscvRegisterName_lt_32 hb
      rw [← h, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at this
      omega
    · rwa [Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega),
        Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)] at h
  · intro t
    by_cases ht : t < 32
    · obtain ⟨n, -, hn⟩ := Flapjack.RiscV.riscvRegisterName_surjective_lt_32 ht
      exact ⟨n, hn⟩
    · exact ⟨t, Flapjack.RiscV.riscvRegisterName_id_of_ge_32 (by omega)⟩

/-- The concrete Lab initializer meets its assumptions for well-formed Stack code. -/
theorem fixtureLab_initAssumptions (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset
      [4] code (fixtureLab code cfg) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
  refine ⟨Or.inr rfl, rfl, rfl, ?_, fixtureLab_memoryAssumption code cfg, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
    good, ?_, by decide, ?_, rfl,rfl,rfl,rfl,rfl,fixtureRegNames_bijective⟩
  · simp [fixtureLab]
  · decide
  · have h : fixtureSavedRegs (StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 0) = false := by
      with_unfolding_all rfl
    simp [fixtureLab,h]
  · simp [fixtureLab]
  · simp [fixtureLab]
  · intro x hx
    change decide (fixtureLabDomain x) = true at hx
    have domain : fixtureLabDomain x := of_decide_eq_true hx
    rcases domain with h | ⟨_,_,aligned⟩
    · subst x; decide
    · exact aligned
  · intro x hx
    change decide (sharedAddress x) = true at hx
    exact (of_decide_eq_true hx).1
  · intro n
    simp [fixtureStackOracle,StackToLab.Proofs.GoodCode.goodCode]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [fixtureSavedRegs]

end SteppedFlapjack.Concrete
