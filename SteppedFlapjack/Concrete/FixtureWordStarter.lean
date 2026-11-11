import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.Concrete.WordStarter
import Flapjack.Misc.Sptree.InsertUnchanged
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
namespace SteppedFlapjack.Concrete

/-- Word initialization over a concrete initialized Stack state and code table. -/
noncomputable def configuredWord (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :=
  makeInit riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (configuredStack code cfg bs) (sptFromAList words) (configuredWordOracle cfg bs)

/-- The original one-bitmap Word initializer. -/
noncomputable def fixtureWord (code : List (Nat × StackLang.HolProg 64))
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) :=
  makeInit riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (fixtureStack code cfg)
    (sptFromAList words) (fixtureWordOracle cfg)

theorem configuredWord_one (code : List (Nat × StackLang.HolProg 64))
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) :
    configuredWord code words cfg [4] = fixtureWord code words cfg := by
  unfold configuredWord fixtureWord
  rw [configuredStack_one,configuredWordOracle_one]

/-- The initialized Stack state uses the backend garbage collector. -/
theorem configuredGc (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :
  (configuredStack code cfg bs).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  unfold configuredStack
  rw [fullMakeInit_eq]
  rfl

/-- The constructed Loop state has the initialized Stack memory domains. -/
theorem configuredLoopDomains (program : Prog (RiscV.Word 64)) (fuel extra : Nat) (body : ProgHOL 64)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 let pan := panSimpSourceState program (clockedFixtureSource program fuel)
 let crep := crepStateFrom pan body
 let timed := {crep with clock := crep.clock + extra}
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).mdomain = (configuredStack code cfg bs).mdomain ∧
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).shMdomain = (configuredStack code cfg bs).shMdomain := by
  classical
  constructor
  · funext a
    apply Bool.eq_iff_iff.mpr
    dsimp only [concreteDeclLoopState]
    rw [decide_eq_true_eq]
    exact (configuredStack_heapDomain code cfg bs fits good a).symm
  · funext a
    apply Bool.eq_iff_iff.mpr
    dsimp only [concreteDeclLoopState]
    rw [decide_eq_true_eq]
    have h := congrFun (configuredStack_ambient code cfg bs fits good).2.2 a
    change sharedAddress a ↔ (configuredStack code cfg bs).shMdomain a = true
    rw [h]
    simp

/-- The constructed Word starter equals the actual native initializer. -/
theorem configuredStarter (program : Prog (RiscV.Word 64)) (fuel extra : Nat) (body : ProgHOL 64)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config) (bs : List (BitVec 64))
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame clock : Nat)
    (frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame) :
 let pan := panSimpSourceState program (clockedFixtureSource program fuel)
 let crep := crepStateFrom pan body
 let timed := {crep with clock := crep.clock + extra}
 {(phase3Starter riscvConfig.isa timed crepPrograms (configuredWord code words cfg bs) fixtureHeapLength 64 frame) with
    memory := (configuredStack code cfg bs).memory, clock := clock, code := (configuredWord code words cfg bs).code} =
 {(configuredWord code words cfg bs) with clock := clock} := by
  classical
  have ambient := configuredStack_ambient code cfg bs fits good
  have current := (configuredStack_heapBaseAndMemory code cfg bs fits good).1
  have len := configuredStack_heapLength code cfg bs fits good
  have fr := sptInsertUnchanged (configuredWord code words cfg bs).stackSize 64 frame frameLookup
  simp only [configuredWord,makeInit] at fr
  have existing {α β : Type} [DecidableEq α] (m : HolFiniteMapExact α β) (k : α) (v : β) (h : m.lookup k = some v) : m.updateEq (k,v) = m := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]
    split
    · rename_i eq
      subst key
      exact h.symm
    · rfl
  have cur : ((configuredStack code cfg bs).store.eraseEq .handler).lookup .currHeap = some (.word heapBase) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using current
  have length : ((configuredStack code cfg bs).store.eraseEq .handler).lookup .heapLength = some (.word fixtureHeapLength) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using len
  simp only [phase3Starter,concreteDeclWordState]
  rw [(configuredLoopDomains program fuel extra body crepPrograms code cfg bs fits good).1,
      (configuredLoopDomains program fuel extra body crepPrograms code cfg bs fits good).2]
  simp [crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
    panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,
    configuredWord,makeInit,configuredGc]
  refine ⟨by rw [existing _ _ _ cur,existing _ _ _ length],fr,?_,?_⟩
  · exact ambient.2.1
  · exact ambient.1.symm
/-- The singleton fixture uses the configured garbage collector. -/
theorem fixtureGc (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) :
    (fixtureStack code cfg).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  have h := configuredGc code cfg [4]
  rw [configuredStack_one] at h
  exact h

theorem fixtureLoopDomains (program : Prog (RiscV.Word 64)) (fuel extra : Nat) (body : ProgHOL 64)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 let pan := panSimpSourceState program (clockedFixtureSource program fuel)
 let crep := crepStateFrom pan body
 let timed := {crep with clock := crep.clock + extra}
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).mdomain = (fixtureStack code cfg).mdomain ∧
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).shMdomain = (fixtureStack code cfg).shMdomain := by
  have fits : 0xa0020018 + ([4] : List (BitVec 64)).length*8 ≤ sourceBase := by decide
  have h := configuredLoopDomains program fuel extra body crepPrograms code cfg [4] fits good
  rw [configuredStack_one] at h
  exact h

theorem fixtureStarter (program : Prog (RiscV.Word 64)) (fuel extra : Nat) (body : ProgHOL 64)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config) (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame clock : Nat)
    (frameLookup : sptLookup 64 (fixtureWord code words cfg).stackSize = some frame) :
 let pan := panSimpSourceState program (clockedFixtureSource program fuel)
 let crep := crepStateFrom pan body
 let timed := {crep with clock := crep.clock + extra}
 {(phase3Starter riscvConfig.isa timed crepPrograms (fixtureWord code words cfg) fixtureHeapLength 64 frame) with
    memory := (fixtureStack code cfg).memory, clock := clock, code := (fixtureWord code words cfg).code} =
 {(fixtureWord code words cfg) with clock := clock} := by
  have fits : 0xa0020018 + ([4] : List (BitVec 64)).length*8 ≤ sourceBase := by decide
  have lookup : sptLookup 64 (configuredWord code words cfg [4]).stackSize = some frame := by
    rw [configuredWord_one]
    exact frameLookup
  have h := configuredStarter program fuel extra body crepPrograms code words cfg [4] fits good frame clock lookup
  rw [configuredWord_one,configuredStack_one] at h
  exact h

end SteppedFlapjack.Concrete
