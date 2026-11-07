import SteppedFlapjack.Concrete.CountedApplications
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

def errorLoop : Prog (RiscV.Word 64) :=
  .seq .skip (.while (.const 1) (.return (.shift .lsl (.const 1) (.const 64))))

theorem errorLoop_supported : Supported errorLoop := by
  constructor
  · exact .seq .skip (.while (.const _) (.ret (.shift .lsl (.const _) (.const _))))
  · simp [errorLoop,ProgByteRanged,ExpByteRanged]

def errorLoopProduction := clockedFixtureProduction errorLoop 4
def errorLoopSource := clockedFixtureSource errorLoop 4

private theorem errorLoopFacts (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    PanSemStateRelExec errorLoopProduction errorLoopSource.toExact ∧
    PanSemStateRelExecRanged errorLoopProduction ∧ WordLocals errorLoopProduction.locals ∧
    evalPanValueFfiProgSteps context primitive handler errorLoopProduction.structs []
      errorLoopProduction.baseAddress errorLoopProduction.topAddress panSemBitVec64BytesInWord 3
      errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi errorLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess errorLoopProduction)) =
        some (.error errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi,4) := by
  have rel : PanSemStateRelExec errorLoopProduction errorLoopSource.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL errorLoop)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have ranged : PanSemStateRelExecRanged errorLoopProduction :=
    PanSemStateRelExecRanged.setClock (source_ranged (progToHOL errorLoop)) 4
  have words : WordLocals errorLoopProduction.locals := by
    intro name value found
    simp [errorLoopProduction,clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found
  have run : evalPanValueFfiProgSteps context primitive handler errorLoopProduction.structs []
      errorLoopProduction.baseAddress errorLoopProduction.topAddress panSemBitVec64BytesInWord 3
      errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi errorLoop
      (memoryAccess := some (panSemBitVec64MemoryAccess errorLoopProduction)) =
        some (.error errorLoopProduction.locals errorLoopProduction.globals errorLoopProduction.memory errorLoopProduction.ffi,4) := by
    simp [errorLoop,evalPanValueFfiProgSteps,panValueIteCondition,panValueReturnSteps,evalPanValueExpCountedWith,
      evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panSemBitVec64MemoryAccess,
      panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,RiscV.panRiscVMemoryModel,RiscV.panRiscVShift]
  exact ⟨rel,ranged,words,run⟩

theorem errorLoop_source_and_simp (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ final,
      errorLoopSource.evaluateHOLFiniteState (progToHOL errorLoop) = (some .error,final) ∧
      errorLoopSource.evaluateHOLFiniteState (progToHOL (panSimpProg errorLoop)) = (some .error,final) ∧
      controlSteps (progToHOL errorLoop) errorLoopSource ≤ 5 := by
  let _ : DecidablePred errorLoopSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  obtain ⟨rel,ranged,words,run⟩ := errorLoopFacts context primitive handler
  obtain ⟨holResult,final,hol,outcome,bound,_⟩ := supported_counted_source errorLoop_supported.1 errorLoopProduction errorLoopSource
    rel ranged words errorLoop_supported.2 context primitive handler [] 3 4 _ run (by rfl)
  cases outcome with
  | error l g m f final nextRel nextRanged nextWords =>
    refine ⟨final,hol,?_,by simpa [countedErrorBonus] using bound⟩
    rw [supported_panSimp_same_state errorLoop errorLoop_supported]
    exact hol
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let body := progToHOL (panSimpProg errorLoop)
    let caller := frontendContext body
    let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let lower := callEntryStateHOLFinite (loweredStateFrom (panSimpSourceState errorLoop errorLoopSource) body) HolFiniteMapExact.empty
    ∃ final, lower.evaluateHOLFiniteState body = (some .error,final) ∧
      controlSteps body lower ≤ sizeOf (compileProgExactHOLW callee body) * 5 := by
  let _ : DecidablePred errorLoopSource.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  obtain ⟨rel,ranged,words,run⟩ := errorLoopFacts context primitive handler
  obtain ⟨holResult,sourceFinal,outcome,lowerRun,bound⟩ := supported_counted_frontend_prefix errorLoop errorLoop_supported
    errorLoopProduction errorLoopSource rel ranged words rfl context primitive handler [] 3 4 4 _ run (by omega) rfl
  cases outcome with
  | error l g m f final nextRel nextRanged nextWords => exact ⟨_,lowerRun,bound⟩
end SteppedFlapjack.Concrete
