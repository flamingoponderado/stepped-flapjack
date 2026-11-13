import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.Concrete.InitEHeap
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.Concrete.WordStarter
import Flapjack.Misc.Sptree.InsertUnchanged
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
namespace SteppedFlapjack.Concrete

/-- Word initialization over a concrete initialized Stack state and code table. -/
noncomputable def configuredWord (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :=
  makeInit riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (configuredStack code cfg bs) (sptFromAList words) (configuredWordOracle cfg bs)

/-- The initialized Stack state uses the backend garbage collector. -/
theorem configuredGc (code : List (Nat × StackLang.HolProg 64)) (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :
  (configuredStack code cfg bs).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  unfold configuredStack
  rw [fullMakeInit_eq]
  rfl

/-- A Crep state with fixture domains and metadata produces the native initialized Word starter. -/
theorem configuredStarter_general (source : CrepSemHOLState 64 Unit)
    (memDomain : source.memaddrs = ordinaryAddress) (sharedDomain : source.shMemaddrs = sharedAddress)
    (base : source.baseAddr = heapBase) (byteOrder : source.be = false) (ffi : source.ffi = sourceFfi)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (code : List (Nat × StackLang.HolProg 64)) (words : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (cfg : LabToTarget.Config) (bs : List (BitVec 64))
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase) (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame clock : Nat)
    (frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame) :
    {(phase3Starter riscvConfig.isa source crepPrograms (configuredWord code words cfg bs) fixtureHeapLength 64 frame) with
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
  have domain : (concreteDeclLoopState riscvConfig.isa source crepPrograms).mdomain = (configuredStack code cfg bs).mdomain := by
    funext a
    apply Bool.eq_iff_iff.mpr
    simpa [concreteDeclLoopState,memDomain] using (configuredStack_heapDomain code cfg bs fits good a).symm
  have shared : (concreteDeclLoopState riscvConfig.isa source crepPrograms).shMdomain = (configuredStack code cfg bs).shMdomain := by
    simp [concreteDeclLoopState,sharedDomain,ambient.2.2]
  simp only [phase3Starter,concreteDeclWordState]
  rw [domain,shared]
  simp [base,byteOrder,ffi,configuredWord,makeInit,configuredGc]
  refine ⟨by rw [existing _ _ _ cur,existing _ _ _ length],fr,?_,?_⟩
  · exact ambient.2.1
  · exact ambient.1.symm

end SteppedFlapjack.Concrete
