import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.DataToWord
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
variable {C F : Type}
/-- Word start state over the Phase 2 memory and code, retaining template fields
needed to match the later native initializer. -/
noncomputable def phase3Starter (arch : AsmArchitecture) (source : CrepSemHOLState 64 F)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64))
    (template : WordSemStateFiniteExact 64 C F) (heapLength : BitVec 64) (start frame : Nat) :
    WordSemStateFiniteExact 64 C F :=
  { concreteDeclWordState arch source programs template heapLength with
    locals := sptInsert 0 (.loc 1 0) .ln
    stack := []
    clock := source.clock + 1
    stackSize := sptInsert start frame template.stackSize
    gcFun := Flapjack.Compiler.Backend.WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf }

/-- The starter discharges the Loop-to-Word data and code relations, return
register, empty-stack and native garbage-collector requirements. -/
theorem phase3Starter_relations (arch : AsmArchitecture) (source : CrepSemHOLState 64 F)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64))
    (template : WordSemStateFiniteExact 64 C F) (heapLength : BitVec 64) (start frame : Nat)
    (memory : BitVec 64 → WordLocW 64) (heap : source.topAddr = source.baseAddr + 2 * heapLength) :
    let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
    let starter := {(phase3Starter arch source programs template heapLength start frame) with memory := memory}
    let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
    loopToWordStateRelHOLExact loop word ∧
    getVar 0 starter = some (.loc 1 0) ∧ starter.stack = [] ∧
    Flapjack.Compiler.Backend.WordSimp.gcFunConstOk starter.gcFun := by
  let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
  let starter := {(phase3Starter arch source programs template heapLength start frame) with memory := memory}
  let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
  have data := (concreteDecl_word_data arch source programs template heapLength heap).1
  have rel := wholeCrepLoopWord_codeRel arch programs
  refine ⟨?_,?_,rfl,?_⟩
  · obtain ⟨len,hm,hd,hs,hc,hbe,hffi,hbase,hlen,htop,hglobals⟩ := data
    refine ⟨len,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals simp_all [phase3Starter,WordSemStateFiniteExact.callEnv,
      WordSemStateFiniteExact.decClock,concreteDeclWordState,concreteDeclLoopState]
  · simp [phase3Starter,WordSemStateFiniteExact.getVar,sptLookup]
  · change Flapjack.Compiler.Backend.WordSimp.gcFunConstOk (Flapjack.Compiler.Backend.WordGcFunctions.wordGcFun countdownRiscVBackend.dataConf)
    exact Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.gcFunConstOkWordGcFun
/-- The starter also meets the generated entry’s locals and context requirements. -/
theorem phase3Starter_locals (arch : AsmArchitecture) (source : CrepSemHOLState 64 F)
    (programs : List (Flapjack.Basis.Pure.MlString.MlString × List Nat × CrepProgHOL 64))
    (template : WordSemStateFiniteExact 64 C F) (heapLength : BitVec 64) (start frame : Nat)
    (p : HolLoopProg 64) (memory : BitVec 64 → WordLocW 64) :
    let loop := {(concreteDeclLoopState arch source programs) with memory := memory}
    let starter := {(phase3Starter arch source programs template heapLength start frame) with memory := memory}
    let word := callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)
    let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln
    LoopToWord.localsRelHOL ctxt loop.locals word.locals ∧
    sptLookup 0 word.locals = some (.loc 1 0) ∧
    (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) := by
  let starter := {(phase3Starter arch source programs template heapLength start frame) with memory := memory}
  have frameLookup : sptLookup start starter.stackSize = some frame := by
    exact sptLookup_sptInsert_same start frame template.stackSize
  have localFacts := SteppedFlapjack.WordToStackSteps.nativeTailEntry_loopLocals p (decClock starter) frame
  dsimp only
  change LoopToWord.localsRelHOL _ (concreteDeclLoopState arch source programs).locals
    (callEnv [(.loc 1 0 : WordLocW 64)] (sptLookup start starter.stackSize) (decClock starter)).locals ∧ _
  rw [frameLookup]
  simp only [concreteDeclLoopState]
  exact ⟨localFacts.1,by simp [WordSemStateFiniteExact.callEnv,sptFromList2,sptLookup],localFacts.2⟩

end SteppedFlapjack.Concrete
