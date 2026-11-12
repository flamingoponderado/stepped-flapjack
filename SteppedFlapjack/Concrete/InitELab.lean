import SteppedFlapjack.Concrete.FixtureCodeMemory
import Flapjack.Compiler.Backend.RiscVConfig.Proofs
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.RiscVConfig

namespace SteppedFlapjack.Concrete

/-- The fixture uses the exact heap limit passed by the native backend. -/
theorem fixture_backend_maxHeap :
    2 * DataToWord.maxHeapLimit 64 countdownRiscVBackend.dataConf - 1 = 2^53-1 := by
  decide +kernel

/-- The label-removal result used to load this exact Stack program. -/
noncomputable def fixtureCodeBytes (code : List (Nat × HolProg 64)) : List (BitVec 8) :=
  match LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf
        (2^53-1) 24 riscvConfig.addrOffset code)) with
  | some (code2,_) => LabToTarget.progToBytes code2
  | none => []

/-- The machine starts immediately before the fixture's code buffer. -/
noncomputable def fixtureCodeStart (code : List (Nat × HolProg 64)) : BitVec 64 :=
  0x800f0134 - BitVec.ofNat 64 (fixtureCodeBytes code).length

/-- Initial memory agrees on the fixture domain and contains loaded code elsewhere. -/
noncomputable def fixtureLabMemoryFor (code : List (Nat × HolProg 64)) (a : BitVec 64) : WordLocW 64 :=
  if fixtureLabDomain a then fixtureLabMemory a else .word (fixtureLoadedWords (fixtureCodeStart code) (fixtureCodeBytes code) a)

/-- The emitted bytes end exactly at the fixture's existing code buffer. -/
theorem fixtureCodeStart_add_length (code : List (Nat × HolProg 64)) :
    fixtureCodeStart code + BitVec.ofNat 64 (fixtureCodeBytes code).length = 0x800f0134 := by
  simp [fixtureCodeStart]

/-- A fitting stream has the expected natural entry address. -/
theorem fixtureCodeStart_toNat (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 0x800f0134) :
    (fixtureCodeStart code).toNat = 0x800f0134 - (fixtureCodeBytes code).length := by
  have small : (BitVec.ofNat 64 (fixtureCodeBytes code).length).toNat = (fixtureCodeBytes code).length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hle : BitVec.ofNat 64 (fixtureCodeBytes code).length ≤ (0x800f0134 : BitVec 64) := by
    rw [BitVec.le_def,small]
    exact fits
  rw [fixtureCodeStart,BitVec.toNat_sub_of_le hle,small]
  rfl

/-- Word-sized encoded instructions give a word-aligned machine entry. -/
theorem fixtureCodeStart_aligned (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 0x800f0134)
    (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    (fixtureCodeStart code).toNat % 4 = 0 := by
  rw [fixtureCodeStart_toNat code fits]
  omega

/-- A code stream of at most 60 KiB ends below the bitmap. -/
theorem fixtureCodeStart_fits (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 61440) :
    (fixtureCodeStart code).toNat + (fixtureCodeBytes code).length ≤ 0xa0020018 := by
  have hle : BitVec.ofNat 64 (fixtureCodeBytes code).length ≤ (0x800f0134 : BitVec 64) := by
    rw [BitVec.le_def,BitVec.toNat_ofNat]
    have small : (fixtureCodeBytes code).length < 2^64 := by omega
    rw [Nat.mod_eq_of_lt small]
    change (fixtureCodeBytes code).length ≤ 0x800f0134
    omega
  unfold fixtureCodeStart
  rw [BitVec.toNat_sub_of_le hle,BitVec.toNat_ofNat]
  have small : (fixtureCodeBytes code).length < 2^64 := by omega
  rw [Nat.mod_eq_of_lt small]
  change 0x800f0134 - (fixtureCodeBytes code).length + (fixtureCodeBytes code).length ≤ 0xa0020018
  omega

/-- Concrete heap and stack pointer registers for the Lab initializer. -/
def fixtureLabRegs (r : Nat) : WordLocW 64 :=
  if r = 11 then .word heapBase else if r = 12 then .word (BitVec.ofNat 64 heapEnd)
  else if r = 13 then .word (BitVec.ofNat 64 ramEnd) else .word 0

/-- The init-e-shaped Lab state for an arbitrary native Stack code table. -/
noncomputable def fixtureLab (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) : LabSem.State 64 LabToTarget.Config Unit where
  regs := fixtureLabRegs
  fpRegs := fun _ => 0
  memory := fixtureLabMemoryFor code
  memDomain := fun a => decide (fixtureLabDomain a)
  sharedMemDomain := fun a => decide (sharedAddress a)
  pc := 0
  be := false
  ffi := sourceFfi
  ioRegs := fun _ _ _ => none
  ccRegs := fun _ _ => none
  ioFpRegs := fun _ _ => 0
  ccFpRegs := fun _ _ => 0
  code := StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset code
  compile := LabToTarget.compile riscvConfig
  compileOracle := fun _ => (cfg,StackToLab.compileNoStubs countdownRiscVBackend.stackConf.regNames countdownRiscVBackend.stackConf.jump riscvConfig.addrOffset 24 [])
  codeBuffer := ⟨0x800f0134,[],0xecc⟩
  clock := 0
  failed := false
  ptrReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 1
  lenReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2
  ptr2Reg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3
  len2Reg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4
  linkReg := StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 0

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs

/-- The configured bitmap and the aligned heap/stack form the Lab memory domain. -/
def configuredLabDomain (bs : List (BitVec 64)) (a : BitVec 64) : Prop :=
  bitmapDomain bs.length a ∨ (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0)
instance (bs : List (BitVec 64)) (a : BitVec 64) : Decidable (configuredLabDomain bs a) := by
  unfold configuredLabDomain
  infer_instance

/-- The real initialized image with a compiler-provided bitmap list. -/
noncomputable def configuredLabMemory (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (a : BitVec 64) : WordLocW 64 :=
  if configuredLabDomain bs a then bitmapMemory bs (fun x => .word (initialWordFor bs.length x)) a
  else .word (countdownWriteCode (fixtureCodeStart code) (fixtureCodeBytes code)
    (bitmapInitialWords bs (initialWordFor bs.length)) a)

noncomputable def configuredLab (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) : LabSem.State 64 LabToTarget.Config Unit :=
  {(fixtureLab code cfg) with memory := configuredLabMemory code bs, memDomain := fun a => decide (configuredLabDomain bs a)}

theorem configuredLab_heapRead (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (a : BitVec 64) (heap : sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0) :
    (configuredLab code cfg bs).memory a = .word (initialWordFor bs.length a) := by
  have domain : configuredLabDomain bs a := Or.inr heap
  have outside : ¬ bitmapDomain bs.length a := by
    intro h
    exact bitmapDomain_disjoint bs.length fits a h ((fixtureLabHeap_addresses a).mp heap)
  simp [configuredLab,configuredLabMemory,domain,bitmapMemory,outside]

theorem configuredLab_separated (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) :
    SetSep.star (Misc.wordList fixtureBitmapBase (bs.map WordLocW.word))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set ((configuredLab code cfg bs).memory,configuredLabDomain bs)) := by
  have graph : SetSep.fun2Set ((configuredLab code cfg bs).memory,configuredLabDomain bs) =
      SetSep.fun2Set (bitmapMemory bs (fun x => .word (initialWordFor bs.length x)),
        fun a => bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a) := by
    funext pair
    rcases pair with ⟨a,w⟩
    apply propext
    simp only [SetSep.fun2SetThm]
    have dom : configuredLabDomain bs a ↔ bitmapDomain bs.length a ∨ addresses heapBase fixtureLabHeapWords a := by
      simp [configuredLabDomain,← fixtureLabHeap_addresses]
    constructor <;> intro ⟨h,d⟩
    · have actual : configuredLabDomain bs a := d
      exact ⟨by simpa [configuredLab,configuredLabMemory,actual] using h,dom.mp d⟩
    · have actual := dom.mpr d
      exact ⟨by simpa [configuredLab,configuredLabMemory,actual] using h,actual⟩
  rw [graph]
  exact bitmapMemory_separated bs (fun x => .word (initialWordFor bs.length x)) fits

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem configuredLab_memoryAssumption (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) :
    StackToLab.Proofs.MakeInit.memoryAssumption countdownRiscVBackend.stackConf.regNames bs 0 (configuredLab code cfg bs) := by
  refine ⟨heapBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd,fixtureBitmapBase,?_⟩
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have r3 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3 = 12 := by with_unfolding_all rfl
  have r4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := by with_unfolding_all rfl
  have heapCount : ((-1 * heapBase + BitVec.ofNat 64 ramEnd).toNat / (StackRemove.bytesInWord 64).toNat) = fixtureLabHeapWords := by decide
  have h0 : sourceBase ≤ heapBase.toNat ∧ heapBase.toNat < ramEnd ∧ heapBase.toNat % 8 = 0 := by decide
  have h1 : sourceBase ≤ (heapBase + bytesInWord 64).toNat ∧ (heapBase + bytesInWord 64).toNat < ramEnd ∧ (heapBase + bytesInWord 64).toNat % 8 = 0 := by decide
  have h2 : sourceBase ≤ (heapBase + 2*bytesInWord 64).toNat ∧ (heapBase + 2*bytesInWord 64).toNat < ramEnd ∧ (heapBase + 2*bytesInWord 64).toNat % 8 = 0 := by decide
  have h3 : sourceBase ≤ (heapBase + 3*bytesInWord 64).toNat ∧ (heapBase + 3*bytesInWord 64).toNat < ramEnd ∧ (heapBase + 3*bytesInWord 64).toNat % 8 = 0 := by decide
  have h4 : sourceBase ≤ (heapBase + 4*bytesInWord 64).toNat ∧ (heapBase + 4*bytesInWord 64).toNat < ramEnd ∧ (heapBase + 4*bytesInWord 64).toNat % 8 = 0 := by decide
  have sep := configuredLab_separated code cfg bs fits
  simp only [configuredLab,fixtureLab,r2,r3,r4,fixtureLabRegs]
  have memEq : ∀ a, (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd ∧ a.toNat % 8 = 0) →
      configuredLabMemory code bs a = .word (initialWordFor bs.length a) := by
    intro a h
    exact configuredLab_heapRead code cfg bs fits a h
  rw [memEq _ h0,memEq _ h1,memEq _ h2,memEq _ h3,memEq _ h4]
  have heads := initialWordFor_headers bs.length
  have endEq : fixtureBitmapBase + bytesInWord 64 * BitVec.ofNat 64 bs.length =
      (0xa0020018 : BitVec 64) + BitVec.ofNat 64 (bs.length*8) := by
    simp [fixtureBitmapBase,bytesInWord,← BitVec.ofNat_mul_ofNat,Nat.mul_comm]
  have zero := (WordListExists.wordListExistsThm (β := WordLocW 64)
    (fixtureBitmapBase + bytesInWord 64 * BitVec.ofNat 64 bs.length) 0).1
  have separated : SetSep.star
      (SetSep.star (Misc.wordList fixtureBitmapBase (bs.map WordLocW.word))
        (Misc.wordListExists (fixtureBitmapBase + bytesInWord 64 * BitVec.ofNat 64 bs.length) 0))
      (Misc.wordListExists heapBase fixtureLabHeapWords)
      (SetSep.fun2Set (configuredLabMemory code bs,fun a => decide (configuredLabDomain bs a) = true)) := by
    rw [zero,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft]
    simpa [configuredLab] using sep
  refine ⟨by decide,by decide,by decide,?_,?_,?_,?_,?_,by trivial,by decide,?_,?_,?_,by decide,?_⟩
  · simpa [fixtureBitmapBase] using heads.1
  · rw [endEq]
    simpa [bytesInWord] using heads.2.1
  · simp only [BitVec.mul_zero,BitVec.add_zero]
    rw [endEq]
    simpa [bytesInWord] using heads.2.2.1
  · simpa [bytesInWord] using heads.2.2.2.1
  · simpa [bytesInWord] using heads.2.2.2.2
  · rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide
  · rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide
  · rw [Flapjack.Pancake.Proofs.PanToTarget.holByteAligned_iff_mod (Or.inr rfl)]; decide
  · simpa only [decide_eq_true_eq,heapCount] using separated

/-- The previous one-bitmap fixture is an instance of the configured layout. -/
theorem configuredLab_one (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    configuredLab code cfg [4] = fixtureLab code cfg := by
  have domain : configuredLabDomain [4] = fixtureLabDomain := by
    funext a
    simp [configuredLabDomain,bitmapDomain_singleton,fixtureLabDomain]
  have memory : configuredLabMemory code [4] = fixtureLabMemoryFor code := by
    funext a
    simp only [configuredLabMemory,domain,fixtureLabMemoryFor]
    rw [show (fun x => WordLocW.word (initialWordFor ([4] : List (BitVec 64)).length x)) =
      (fun x => WordLocW.word (initialWord x)) by simp [initialWordFor_one]]
    rw [bitmapMemory_singleton]
    simp only [List.length_cons,List.length_nil,Nat.zero_add,initialWordFor_one,bitmapInitialWords_singleton,fixtureLoadedWords]
  have dom : (fun a => decide (configuredLabDomain [4] a)) = (fixtureLab code cfg).memDomain := by
    change (fun a => decide (configuredLabDomain [4] a)) = (fun a => decide (fixtureLabDomain a))
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Iff.of_eq (congrFun domain a)
  unfold configuredLab
  rw [memory,dom]
  rfl


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

/-- Full initialization assumptions for any fitting compiler bitmap list. -/
theorem configuredLab_initAssumptions (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
      bs code (configuredLab code cfg bs) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
  refine ⟨Or.inr rfl, rfl, rfl, ?_, configuredLab_memoryAssumption code cfg bs fits, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
    good, ?_, by decide, ?_, rfl,rfl,rfl,rfl,rfl,fixtureRegNames_bijective⟩
  · simp [configuredLab,fixtureLab]
  · decide
  · have h : fixtureSavedRegs (StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 0) = false := by
      with_unfolding_all rfl
    simp [configuredLab,fixtureLab,h]
  · simp [configuredLab,fixtureLab]
  · simp [configuredLab,fixtureLab]
  · intro x hx
    change decide (configuredLabDomain bs x) = true at hx
    have domain : configuredLabDomain bs x := of_decide_eq_true hx
    rcases domain with h | h
    · exact h.2.2
    · exact h.2.2
  · intro x hx
    change decide (sharedAddress x) = true at hx
    exact (of_decide_eq_true hx).1
  · intro n
    simp [fixtureStackOracle,StackToLab.Proofs.GoodCode.goodCode]
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [fixtureSavedRegs]

end SteppedFlapjack.Concrete
