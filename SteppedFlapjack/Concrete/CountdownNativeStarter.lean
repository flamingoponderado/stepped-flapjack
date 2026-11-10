import SteppedFlapjack.Concrete.CountdownInitE
import Flapjack.Misc.Sptree.InsertUnchanged
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
namespace SteppedFlapjack.Concrete

theorem countdownFixture_gc (n : Nat) (cfg : LabToTarget.Config) :
  (countdownFixtureStack n cfg).gcFun = WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf := by
  unfold countdownFixtureStack fixtureStack
  rw [fullMakeInit_eq]
  rfl
end SteppedFlapjack.Concrete
namespace SteppedFlapjack.Concrete
open SteppedFlapjack.LoopToWordSteps Flapjack.Compiler.Backend.WordToStack.Native.Initialization
noncomputable def countdownFixtureWord (n : Nat) (cfg : LabToTarget.Config) :=
  makeInit riscvConfig countdownZeroLimit (countdownFixtureStack n cfg)
    (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2)
    (fixtureWordOracle cfg)

theorem countdownFixture_entryFrame (n : Nat) (cfg : LabToTarget.Config) : sptLookup 64 (countdownFixtureWord n cfg).stackSize = some 0 := by
  change sptLookup 64 (sptMapi _ (sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2)) = _
  rw [countdown_optimized_literal, sptLookupMapi, sptLookup_sptFromAList]
  simp [countdownOptimizedLiteral, sptAListLookup, WordToStack.Native.compileProgNative, maxVarHOL, countdownZeroLimit]
  constructor <;> with_unfolding_all rfl
end SteppedFlapjack.Concrete
namespace SteppedFlapjack.Concrete
open SteppedFlapjack.LoopToWordSteps Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem countdownFixture_loopDomain (n : Nat) (cfg : LabToTarget.Config) :
 let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
 let crep := crepStateFrom pan (naturalCountdownHOL n)
 let timed := {crep with clock := crep.clock + countdownLoopBudget n}
 (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)).mdomain = (countdownFixtureStack n cfg).mdomain := by
  classical
  funext a
  apply Bool.eq_iff_iff.mpr
  dsimp only [concreteDeclLoopState]
  rw [decide_eq_true_eq]
  exact (fixtureStack_heapDomain (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n) a).symm

theorem countdownFixture_loopShared (n : Nat) (cfg : LabToTarget.Config) :
 let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
 let crep := crepStateFrom pan (naturalCountdownHOL n)
 let timed := {crep with clock := crep.clock + countdownLoopBudget n}
 (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)).shMdomain = (countdownFixtureStack n cfg).shMdomain := by
  classical
  funext a
  apply Bool.eq_iff_iff.mpr
  dsimp only [concreteDeclLoopState]
  rw [decide_eq_true_eq]
  have h := congrFun (fixtureStack_ambient (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n)).2.2 a
  change (fixtureStack (countdownNativeStackCode n) cfg).shMdomain a = decide (sharedAddress a) at h
  change sharedAddress a ↔ (fixtureStack (countdownNativeStackCode n) cfg).shMdomain a = true
  rw [h]
  simp

theorem countdownFixture_starter_eq (n c : Nat) (cfg : LabToTarget.Config) :
  {(countdownWordStarter n (countdownFixtureWord n cfg) 0) with memory := (countdownFixtureStack n cfg).memory, clock := c, code := (countdownFixtureWord n cfg).code} = {(countdownFixtureWord n cfg) with clock := c} := by
  classical
  have ambient := fixtureStack_ambient (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n)
  have current := (fixtureStack_heapBaseAndMemory (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n)).1
  have len := fixtureStack_heapLength (countdownNativeStackCode n) cfg (countdown_nativeGoodCode n)
  have fr := sptInsertUnchanged (countdownFixtureWord n cfg).stackSize 64 0 (countdownFixture_entryFrame n cfg)
  simp only [countdownFixtureWord,makeInit] at fr
  have existing {α β : Type} [DecidableEq α] (m : HolFiniteMapExact α β) (k : α) (v : β) (h : m.lookup k = some v) : m.updateEq (k,v) = m := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp only [HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]
    split
    · rename_i eq
      subst key
      exact h.symm
    · rfl
  have cur : ((countdownFixtureStack n cfg).store.eraseEq .handler).lookup .currHeap = some (.word heapBase) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL,countdownFixtureStack] using current
  have length : ((countdownFixtureStack n cfg).store.eraseEq .handler).lookup .heapLength = some (.word fixtureHeapLength) := by
    simpa [HolFiniteMapExact.lookup_eraseEq,FDOMSUB_HOL,countdownFixtureStack] using len
  simp only [countdownWordStarter,phase3Starter,concreteDeclWordState]
  rw [countdownFixture_loopDomain n cfg,countdownFixture_loopShared n cfg]
  simp [    crepStateFrom,concreteDeclCrepState,loweredStateFrom,noGlobalsLoweredPreCall,
    panSimpSourceState,clockedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,
    countdownFixtureWord,makeInit,countdownFixture_gc]
  refine ⟨by rw [existing _ _ _ cur,existing _ _ _ length],fr,?_,?_⟩
  · exact ambient.2.1
  · exact ambient.1.symm

/-- The counted source reaches the optimized Word start call from the actual
native initializer, with an explicit Word visit bound. -/
theorem countdownFixture_native_word (n : Nat) (range : n < 2^64) (cfg : LabToTarget.Config)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
    let crep := crepStateFrom pan (naturalCountdownHOL n)
    let word := {(countdownFixtureWord n cfg) with clock := 6*countdownLoopVisits n+1}
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) word
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 0]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none) word ≤ countdownWordBound n := by
  have h := countdownFixture_initialized_word n range cfg context primitive handler (countdownFixtureWord n cfg) 0
  have codeEq : (countdownFixtureWord n cfg).code = sptFromAList (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2 := rfl
  dsimp only at h
  rw [← codeEq, countdownFixture_starter_eq] at h
  exact h

end SteppedFlapjack.Concrete
