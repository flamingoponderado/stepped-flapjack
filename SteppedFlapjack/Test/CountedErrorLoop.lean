import SteppedFlapjack.Concrete.CountedApplications
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

def errorLoop : Prog (RiscV.Word 64) :=
  .dec "x" .one (.const 2) (.while (.const 1)
    (.ite (.var .local "x") (.assign .local "x" (.const 0))
      (.return (.shift .lsl (.const 1) (.const 64)))))

theorem errorLoop_supported : Supported errorLoop := by
  constructor
  · exact .decl "x" (.const _) (.while (.const _) (.ite (.local "x" (by simp))
      (.assign "x" (by simp) (.const _)) (.ret (.shift .lsl (.const _) (.const _)))))
  · simp [errorLoop,ProgByteRanged,ExpByteRanged,NameRanged,ShapeByteRanged]

def errorLoopProduction := clockedFixtureProduction errorLoop 12
def errorLoopSource := clockedFixtureSource errorLoop 12

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4000 in
private theorem errorLoopFacts (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    PanSemStateRelExec errorLoopProduction errorLoopSource.toExact ∧
    PanSemStateRelExecRanged errorLoopProduction ∧ WordLocals errorLoopProduction.locals ∧
    evalPanValueFfiProgSteps context primitive handler errorLoopProduction.structs []
      errorLoopProduction.baseAddress errorLoopProduction.topAddress panSemBitVec64BytesInWord 7
      errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi errorLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess errorLoopProduction)) =
        some (.error errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi,12) := by
  obtain ⟨rel,ranged,words⟩ := clockedFixture_premises errorLoop 12
  have run : evalPanValueFfiProgSteps context primitive handler errorLoopProduction.structs []
      errorLoopProduction.baseAddress errorLoopProduction.topAddress panSemBitVec64BytesInWord 7
      errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi errorLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess errorLoopProduction)) =
        some (.error errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi,12) := by
    simp (config := {maxSteps := 1000000}) [errorLoop,evalPanValueFfiProgSteps,panValueDecAccepted,
      panValueAssignLocalResult,panValueIteCondition,panValueReturnResult,evalPanValueExpCountedWith,
      evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panSemBitVec64MemoryAccess,
      panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,errorLoopProduction,clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction,
      RiscV.panRiscVMemoryModel,RiscV.panRiscVShift,updatePanValueMap,restorePanValueFfiLocal,
      panShapeMatches,panValueShape,panValueAssignmentValid]
    funext name
    by_cases same : name = "x" <;> simp [restorePanValueLocal,updatePanValueMap,same]
  exact ⟨rel,ranged,words,run⟩

theorem errorLoop_source_and_simp (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      errorLoopSource.evaluateHOLFiniteState (progToHOL errorLoop) = (some .error,final) ∧
      errorLoopSource.evaluateHOLFiniteState (progToHOL (panSimpProg errorLoop)) = (some .error,final) ∧
      controlSteps (progToHOL errorLoop) errorLoopSource ≤ 13 := by
  let _ : DecidablePred errorLoopSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  obtain ⟨rel,ranged,words,run⟩ := errorLoopFacts context primitive handler
  obtain ⟨holResult,final,hol,outcome,bound,_⟩ := supported_counted_source errorLoop_supported.1 errorLoopProduction errorLoopSource
    rel ranged words errorLoop_supported.2 context primitive handler [] 7 12 _ run (by rfl)
  cases outcome with
  | error l g m f final nextRel nextRanged nextWords =>
    refine ⟨final,hol,?_,by simpa [countedErrorBonus] using bound⟩
    rw [supported_panSimp_same_state errorLoop errorLoop_supported]
    exact hol
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let body := progToHOL (panSimpProg errorLoop)
    let entry : CrepProgHOL 64 := .seq .skip (.call none (entryName body) [])
    ∃ final, evalCrepSemHOLProgExact
      (crepStateFrom (panSimpSourceState errorLoop errorLoopSource) body) entry = (some .error,final) ∧
      CrepSteps.steps entry (crepStateFrom (panSimpSourceState errorLoop errorLoopSource) body) ≤ 423 := by
  let _ : DecidablePred errorLoopSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  obtain ⟨rel,ranged,words,run⟩ := errorLoopFacts context primitive handler
  obtain ⟨exit,final,outcome,target,bound⟩ := supported_counted_full_frontend_uniform errorLoop errorLoop_supported
    errorLoopProduction errorLoopSource rel ranged words rfl rfl rfl rfl context primitive handler [] 7 12 12 _ run (by omega) rfl
  cases outcome with
  | error l g m f =>
    have weight : CrepSteps.statementWeight (compileProgExactHOLW
      (ctxtFcExactHOL (frontendContext (progToHOL (panSimpProg errorLoop))).funcs
        (frontendContext (progToHOL (panSimpProg errorLoop))).eids [] [] [])
      (progToHOL (panSimpProg errorLoop))) = 7 := by
      simp only [errorLoop,panSimpProg,seqAssoc,smartSeq,retToTail,progToHOL,expToHOL,shapeToHOL]
      simp_crep_code
      simp [CrepSteps.statementWeight]
    rw [weight] at bound
    exact ⟨final,target,by simpa using bound⟩
end SteppedFlapjack.Concrete
