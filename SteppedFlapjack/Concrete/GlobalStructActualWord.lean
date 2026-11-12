import SteppedFlapjack.Concrete.GlobalStructActualOptimizedLoop
import SteppedFlapjack.Concrete.WordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.LoopToWordSteps.WholeWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps

def globalStructActualWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa globalStructCallPrograms)
def globalStructActualWordContext := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
  (sptDifference (accVarsHOL globalStructActualOptimizedLoop .ln) (LoopToWord.toNumSetHOL []))) .ln

def globalStructActualClockedCrep := {globalStructCallCrep with clock := globalStructCallCrep.clock + globalStructActualLoopClock}

noncomputable def globalStructActualWordStarter {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :=
  phase3Starter riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms template fixtureHeapLength firstLoopName frame

theorem globalStruct_actualWordEntry :
    (firstLoopName,1,(LoopToWord.compHOL globalStructActualWordContext globalStructActualOptimizedLoop (firstLoopName,2)).1) ∈ globalStructActualWordPrograms := by
  obtain ⟨tail,first⟩ := globalStruct_actualLoop_first
  unfold globalStructActualWordPrograms
  rw [first]
  simp [loopToWordCompileHOL,loopToWordCompileProgHOL,loopToWordCompFuncHOL,globalStructActualWordContext,globalStructActualOptimizedLoop]

theorem globalStruct_actualWord_unique : (globalStructActualWordPrograms.map Prod.fst).Nodup := by
  simpa [globalStructActualWordPrograms,loopToWordCompileHOL,loopToWordCompileProgHOL,List.map_map,Function.comp_def] using
    firstCompileProgAllDistinctExact riscvConfig.isa globalStructCallPrograms

theorem globalStruct_actualWord_heap : globalStructActualClockedCrep.topAddr =
    globalStructActualClockedCrep.baseAddr + 2 * fixtureHeapLength := by
  change heapTop = heapBase + 2 * fixtureHeapLength
  decide


noncomputable def globalStructActualWordStarterWithMemory {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) (memory : BitVec 64 → WordLocW 64) :=
  {globalStructActualWordStarter template frame with memory := memory}

theorem globalStruct_actualWord_run_withMemory {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact globalStructCallCrep.memory memory globalStructCallCrep.memaddrs) :
    let starter := globalStructActualWordStarterWithMemory template frame memory
    let final := WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none)
      {starter with clock := 6*globalStructActualOptimizedLimit+1, code := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile phase3WordConfig riscvConfig globalStructActualWordPrograms).2}
    final.1 = some (.result (.loc 1 0) [.word 8]) ∧
      WordSteps.steps (.call none (some firstLoopName) [0] none)
        {starter with clock := 6*globalStructActualOptimizedLimit+1, code := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile phase3WordConfig riscvConfig globalStructActualWordPrograms).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable
          phase3WordConfig riscvConfig globalStructActualWordPrograms).2)) * (6*globalStructActualOptimizedLimit+1) := by
  classical
  obtain ⟨crepPost,loopPost,crepRun,loopRun,loopBound⟩ := globalStruct_actualOptimizedLoop_run_withMemory memory memoryRel
  have relations := phase3Starter_relations riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms
    template fixtureHeapLength firstLoopName frame memory globalStruct_actualWord_heap
  have localFacts := phase3Starter_locals riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms
    template fixtureHeapLength firstLoopName frame globalStructActualOptimizedLoop memory
  have starterEq : {(phase3Starter riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms
      template fixtureHeapLength firstLoopName frame) with memory := memory} = globalStructActualWordStarterWithMemory template frame memory := by
    rfl
  rw [starterEq] at relations localFacts
  have loopEq : {(concreteDeclLoopState riscvConfig.isa globalStructActualClockedCrep globalStructCallPrograms) with memory := memory} =
      {globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock} := by
    simp [globalStructActualLoopState,globalStructActualClockedCrep,concreteDeclLoopState]
    constructor <;> funext address <;> apply Bool.eq_iff_iff.mpr
    · by_cases h : globalStructCallCrep.memaddrs address <;> simp [h]
    · by_cases h : globalStructCallCrep.shMemaddrs address <;> simp [h]
  rw [loopEq] at relations localFacts
  have shape : SimpleLoopSequenceSource globalStructActualOptimizedLoop := by
    apply optimise_simpleSequence
    unfold globalStructActualEntryLoop globalStructActualEntryCrep
    rw [← globalStruct_actualPan_compiled]
    exact callFrontend_compiled_loopShape globalStruct_actualPan_shape _ _
  have table : LoopTableSupported ({globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock}).code :=
    callFrontend_compiled_loopTableSupported riscvConfig.isa globalStructCallPrograms globalStruct_actualCode_sources
  have run := loopTable_wholeWord_span shape
    {globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock}
    loopPost (some (.result [.word 8])) table firstLoopName (globalStructActualWordStarterWithMemory template frame memory)
    globalStructActualWordContext (firstLoopName,2) globalStructActualOptimizedLimit globalStructActualWordPrograms
    phase3WordConfig riscvConfig globalStruct_actualWordEntry globalStruct_actualWord_unique
    (loopToWord_programSafety _) (by rfl)
    relations.2.1
    relations.2.2.1
    relations.2.2.2
    ⟨loopRun,by simp,relations.1,
      by simpa [globalStructActualWordContext] using localFacts.1,
      localFacts.2.1,Or.inr rfl,by decide,
      by simpa [globalStructActualWordContext] using localFacts.2.2⟩ (.return _) loopBound
  obtain ⟨wordPost,wordResult,resultRel,success,_,steps⟩ := run
  have resultEq : wordResult = some (.result (.loc 1 0) [.word 8]) := resultRel.2.1
  exact ⟨success.trans resultEq,steps⟩


/-- The actual global entry reaches optimized Word with a code-derived bound. -/
theorem globalStruct_actualWord_run {C : Type} (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let starter := globalStructActualWordStarter template frame
    let final := WordSemStateFiniteExact.evaluate (.call none (some firstLoopName) [0] none)
      {starter with clock := 6*globalStructActualOptimizedLimit+1, code := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile phase3WordConfig riscvConfig globalStructActualWordPrograms).2}
    final.1 = some (.result (.loc 1 0) [.word 8]) ∧
      WordSteps.steps (.call none (some firstLoopName) [0] none)
        {starter with clock := 6*globalStructActualOptimizedLimit+1, code := sptFromAList (Flapjack.Compiler.Backend.WordToWord.compile phase3WordConfig riscvConfig globalStructActualWordPrograms).2} ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable
          phase3WordConfig riscvConfig globalStructActualWordPrograms).2)) * (6*globalStructActualOptimizedLimit+1) := by
  have relations := concreteDecl_crepLoop_relations riscvConfig.isa globalStructCallCrep globalStructCallPrograms rfl
  have h := globalStruct_actualWord_run_withMemory template frame globalStructActualLoopState.memory (by
    simpa [globalStructActualLoopState] using relations.2.1)
  simpa [globalStructActualWordStarterWithMemory,globalStructActualWordStarter,phase3Starter,
    concreteDeclWordState,globalStructActualLoopState,globalStructActualClockedCrep,concreteDeclLoopState] using h

end SteppedFlapjack.Concrete
