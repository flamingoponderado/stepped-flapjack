import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.Concrete.BranchingLoop
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

def fixtureBody := progToHOL (panSimpProg branchingLoop)
def fixtureCallee := ctxtFcExactHOL (frontendContext fixtureBody).funcs (frontendContext fixtureBody).eids [] [] []
def countedFixtureSource := {(exactState (progToHOL branchingLoop)) with clock := 23}
def countedFixtureProduction := {(executableState (progToHOL branchingLoop)) with clock := 23}

example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branchingLoop countedFixtureSource) fixtureBody)
        (.seq .skip (.call none (entryName fixtureBody) [])) = (some (.return [.word 7]),targetFinal) ∧
      CrepSteps.steps (.seq .skip (.call none (entryName fixtureBody) []))
        (crepStateFrom (panSimpSourceState branchingLoop countedFixtureSource) fixtureBody) ≤
          57627 := by
  have rel : PanSemStateRelExec countedFixtureProduction countedFixtureSource.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL branchingLoop)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have ranged : PanSemStateRelExecRanged countedFixtureProduction :=
    PanSemStateRelExecRanged.setClock (source_ranged (progToHOL branchingLoop)) 23
  have words : WordLocals countedFixtureProduction.locals := by
    intro name value found
    simp [countedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found
  have topOutside : ¬ countedFixtureSource.memaddrs countedFixtureSource.topAddr := by
    simp [countedFixtureSource,exactState,singleEntrySourceTemplate,sourceTemplate,ordinaryAddress,heapTop,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL countedFixtureSource.topAddr := by
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have run := branchingLoop_source_run context primitive handler
  have run' : evalPanValueFfiProgSteps context primitive handler countedFixtureProduction.structs []
      countedFixtureProduction.baseAddress countedFixtureProduction.topAddress panSemBitVec64BytesInWord 7
      countedFixtureProduction.locals countedFixtureProduction.globals countedFixtureProduction.memory countedFixtureProduction.ffi branchingLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess countedFixtureProduction)) =
      some (.returned countedFixtureProduction.locals countedFixtureProduction.globals countedFixtureProduction.memory countedFixtureProduction.ffi [.word 7],23) := by
    simpa [countedFixtureProduction,panSemBitVec64MemoryAccess] using run
  let _ : DecidablePred countedFixtureSource.memaddrs := inferInstanceAs (DecidablePred (exactState (progToHOL branchingLoop)).memaddrs)
  have result := supported_counted_full_frontend branchingLoop branchingLoop_supported countedFixtureProduction countedFixtureSource
    rel ranged words rfl rfl rfl rfl topOutside aligned rfl context primitive handler [] 7 23 23
    countedFixtureProduction.locals countedFixtureProduction.globals countedFixtureProduction.memory countedFixtureProduction.ffi 7
    run' (by omega) rfl
  have lookup := (supported_callee_relations branchingLoop branchingLoop_supported).1
  have codeEq : compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop) = branchingLoopCrepBody := by
    rw [branchingLoop_code_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  have size : sizeOf branchingLoopCrepBody = 49 := by decide
  simp only [branchingLoop_simp_program] at result
  change ∃ final, evalCrepSemHOLProgExact (crepStateFrom (panSimpSourceState branchingLoop countedFixtureSource) (progToHOL branchingLoop))
    (.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])) = (some (.return [.word 7]),final) ∧
    CrepSteps.steps (.seq .skip (.call none (entryName (progToHOL branchingLoop)) []))
      (crepStateFrom (panSimpSourceState branchingLoop countedFixtureSource) (progToHOL branchingLoop)) ≤
        3 + sizeOf (compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop)) *
          (sizeOf (compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop)) * (23+1)) at result
  rw [codeEq,size] at result
  simpa [fixtureBody,branchingLoop_simp_program] using result
end SteppedFlapjack.Concrete
