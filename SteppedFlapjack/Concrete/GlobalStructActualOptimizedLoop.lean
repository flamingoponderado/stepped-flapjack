import SteppedFlapjack.Concrete.GlobalStructActualLoop
import SteppedFlapjack.Concrete.CountedSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps

def globalStructActualEntryCrep : CrepProgHOL 64 := .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])
def globalStructActualEntryLoop : HolLoopProg 64 := compileHOLExact globalStructActualLoopContext .ln globalStructActualEntryCrep

theorem globalStruct_actualEntry_simp : crepSimpProgHOL globalStructActualEntryCrep = globalStructActualEntryCrep := by
  unfold globalStructActualEntryCrep
  rw [← globalStruct_actualPan_compiled]
  exact callFrontend_simp_fixed globalStruct_actualPan_shape

theorem globalStruct_actualLoop_first : ∃ tail,
    compileProgHOLExact riscvConfig.isa globalStructCallPrograms =
      (firstLoopName,[],optimiseHOL globalStructActualEntryLoop) :: tail := by
  have h := firstCrep_loopEntry riscvConfig.isa (ofString "main") globalStructActualEntryCrep
    [(newMainNameHOL globalStructProgram,[],globalStructActualBody)] globalStruct_actualEntry_simp
  simpa [globalStruct_actualPrograms_eq,globalStructActualLoopContext,globalStructActualEntryLoop,
    globalStructActualEntryCrep] using h

theorem globalStruct_actualLoop_lookup :
    sptLookup firstLoopName globalStructActualLoopState.code = some ([],optimiseHOL globalStructActualEntryLoop) := by
  obtain ⟨tail,first⟩ := globalStruct_actualLoop_first
  change sptLookup firstLoopName (sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms)) = _
  rw [first,sptLookup_sptFromAList]
  simp [sptAListLookup]


def globalStructActualOptimizedLoop : HolLoopProg 64 := optimiseHOL globalStructActualEntryLoop

def globalStructActualOptimizedLimit : Nat :=
    loopVisitWeight globalStructActualOptimizedLoop +
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms))+2) * (2 * globalStructActualLoopLimit)

/-- The actual optimizer preserves the real entry execution at an explicit visit bound. -/
theorem globalStruct_actualOptimizedLoop_run_withMemory (memory : BitVec 64 → WordLocW 64)
    (memoryRel : crepToLoopMemRelHOLExact globalStructCallCrep.memory memory globalStructCallCrep.memaddrs) : ∃ crepPost loopPost,
    evalCrepSemHOLProgExact globalStructCallCrep globalStructActualEntryCrep =
      (some (.return [.word 8]),crepPost) ∧
    evaluate globalStructActualOptimizedLoop
      {globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock} =
        (some (.result [.word 8]),loopPost) ∧
    SteppedFlapjack.LoopSteps.steps globalStructActualOptimizedLoop
      {globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock} ≤ globalStructActualOptimizedLimit ∧ loopPost.ffi = sourceFfi := by
  obtain ⟨crepPost,loopPost,crepRun,loopRun,loopBound,loopFfi⟩ := globalStruct_actualLoop_run_withMemory memory memoryRel
  have shape : SimpleLoopSequenceSource globalStructActualEntryLoop := by
    unfold globalStructActualEntryLoop globalStructActualEntryCrep
    rw [← globalStruct_actualPan_compiled]
    exact callFrontend_compiled_loopShape globalStruct_actualPan_shape _ _
  have table : LoopTableSupported globalStructActualLoopState.code :=
    callFrontend_compiled_loopTableSupported riscvConfig.isa globalStructCallPrograms globalStruct_actualCode_sources
  have weight := loopCodeWeight_lookup globalStructActualLoopState.code firstLoopName [] globalStructActualOptimizedLoop globalStruct_actualLoop_lookup
  have bound := optimise_simpleSequence_source_bound shape
    {globalStructActualLoopState with memory := memory, clock := globalStructActualLoopState.clock+globalStructActualLoopClock}
    loopPost (some (.result [.word 8])) (by simpa using table) (by simpa [globalStructActualOptimizedLoop] using Nat.le_trans weight (by omega))
    (by simpa [globalStructActualEntryLoop,globalStructActualEntryCrep] using loopRun) (.return _)
  refine ⟨crepPost,loopPost,by simpa [globalStructActualEntryCrep] using crepRun,?_,?_,loopFfi⟩
  · simpa [globalStructActualOptimizedLoop] using bound.1
  · have code : globalStructActualLoopState.code = sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms) := rfl
    simp only [code] at bound
    simp only [code]
    have steps := Nat.mul_le_mul_left (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa globalStructCallPrograms))+2)
      (Nat.mul_le_mul_left 2 loopBound)
    simpa [globalStructActualOptimizedLoop,globalStructActualOptimizedLimit,globalStructActualEntryLoop,globalStructActualEntryCrep] using Nat.le_trans bound.2 (Nat.add_le_add_left steps _)


/-- The source's own memory is a concrete instance of the optimized run. -/
theorem globalStruct_actualOptimizedLoop_run : ∃ crepPost loopPost,
    evalCrepSemHOLProgExact globalStructCallCrep globalStructActualEntryCrep =
      (some (.return [.word 8]),crepPost) ∧
    evaluate globalStructActualOptimizedLoop
      {globalStructActualLoopState with clock := globalStructActualLoopState.clock+globalStructActualLoopClock} =
        (some (.result [.word 8]),loopPost) ∧
    SteppedFlapjack.LoopSteps.steps globalStructActualOptimizedLoop
      {globalStructActualLoopState with clock := globalStructActualLoopState.clock+globalStructActualLoopClock} ≤ globalStructActualOptimizedLimit ∧ loopPost.ffi = sourceFfi := by
  have relations := concreteDecl_crepLoop_relations riscvConfig.isa globalStructCallCrep globalStructCallPrograms rfl
  have h := globalStruct_actualOptimizedLoop_run_withMemory globalStructActualLoopState.memory (by
    simpa [globalStructActualLoopState] using relations.2.1)
  simpa using h

end SteppedFlapjack.Concrete
