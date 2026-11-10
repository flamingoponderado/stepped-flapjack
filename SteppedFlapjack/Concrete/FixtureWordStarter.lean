import SteppedFlapjack.Concrete.FixtureCrepMemory
import SteppedFlapjack.Concrete.WordStarter
import Flapjack.Misc.Sptree.InsertUnchanged
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
namespace SteppedFlapjack.Concrete

/-- Word initialization over a concrete initialized Stack state and code table. -/
noncomputable def fixtureWord (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) :=
  makeInit riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (fixtureStack code cfg) (sptFromAList words) (fixtureWordOracle cfg)

/-- The initialized Stack state uses the backend garbage collector. -/
theorem fixtureGc (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) :
  (fixtureStack code cfg).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  unfold fixtureStack
  rw [fullMakeInit_eq]
  rfl

/-- The constructed Loop state has the initialized Stack memory domains. -/
theorem fixtureLoopDomains (program : Prog (RiscV.Word 64)) (fuel extra : Nat) (body : ProgHOL 64)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
 let pan := panSimpSourceState program (clockedFixtureSource program fuel)
 let crep := crepStateFrom pan body
 let timed := {crep with clock := crep.clock + extra}
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).mdomain = (fixtureStack code cfg).mdomain ∧
 (concreteDeclLoopState riscvConfig.isa timed crepPrograms).shMdomain = (fixtureStack code cfg).shMdomain := by
  classical
  constructor
  · funext a
    apply Bool.eq_iff_iff.mpr
    dsimp only [concreteDeclLoopState]
    rw [decide_eq_true_eq]
    exact (fixtureStack_heapDomain code cfg good a).symm
  · funext a
    apply Bool.eq_iff_iff.mpr
    dsimp only [concreteDeclLoopState]
    rw [decide_eq_true_eq]
    have h := congrFun (fixtureStack_ambient code cfg good).2.2 a
    change sharedAddress a ↔ (fixtureStack code cfg).shMdomain a = true
    rw [h]
    simp

/-- The constructed Word starter equals the actual native initializer. -/
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
  classical
  have ambient := fixtureStack_ambient code cfg good
  have current := (fixtureStack_heapBaseAndMemory code cfg good).1
  have len := fixtureStack_heapLength code cfg good
  have fr := sptInsertUnchanged (fixtureWord code words cfg).stackSize 64 frame frameLookup
  simp only [fixtureWord,makeInit] at fr
  have existing {α β : Type} [DecidableEq α] (m : HolFiniteMapExact α β) (k : α) (v : β) (h : m.lookup k = some v) : m.updateEq (k,v) = m := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]
    split
    · rename_i eq
      subst key
      exact h.symm
    · rfl
  have cur : ((fixtureStack code cfg).store.eraseEq .handler).lookup .currHeap = some (.word heapBase) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using current
  have length : ((fixtureStack code cfg).store.eraseEq .handler).lookup .heapLength = some (.word fixtureHeapLength) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL] using len
  simp only [phase3Starter,concreteDeclWordState]
  rw [(fixtureLoopDomains program fuel extra body crepPrograms code cfg good).1,
      (fixtureLoopDomains program fuel extra body crepPrograms code cfg good).2]
  simp [crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
    panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,
    fixtureWord,makeInit,fixtureGc]
  refine ⟨by rw [existing _ _ _ cur,existing _ _ _ length],fr,?_,?_⟩
  · exact ambient.2.1
  · exact ambient.1.symm
end SteppedFlapjack.Concrete
