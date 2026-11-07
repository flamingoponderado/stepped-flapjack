import SteppedFlapjack.Concrete.CountedShape
import SteppedFlapjack.Concrete.BranchingLoop
import SteppedFlapjack.Concrete.CountedScalar
import SteppedFlapjack.PanToCrepSteps.CountedInvert
import SteppedFlapjack.Concrete.SourceRuns

namespace SteppedFlapjack.Test
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps

/-- The return inversion premises are met by the concrete source fixture. -/
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    (exactState branchingHOL).evaluateHOLFiniteState (.return (.const 7)) =
      (some (.returned (.val (.word 7))),(exactState branchingHOL).emptyLocalsHOLFinite) ∧
    controlSteps (.return (.const 7)) (exactState branchingHOL) ≤ 2 := by
  have run : evalPanValueFfiProgSteps context primitive handler (executableState branchingHOL).structs []
      (executableState branchingHOL).baseAddress (executableState branchingHOL).topAddress panSemBitVec64BytesInWord 1
      (executableState branchingHOL).locals (executableState branchingHOL).globals (executableState branchingHOL).memory
      (executableState branchingHOL).ffi (.return (.const 7))
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState branchingHOL))) =
      some (.returned (fun _ => none) (executableState branchingHOL).globals (executableState branchingHOL).memory
        (executableState branchingHOL).ffi [.word 7],2) := by
    simp [evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,evalPanValueExpCounted,
      evalPanValueExp,panValueExpStepCost,panValuePayloadWithinLimit,panValuePayloadSizeFuel]
  have words : WordLocals (executableState branchingHOL).locals := by
    simpa [executableState,singleEntrySourceProduction,sourceProduction] using wordLocals_empty
  obtain ⟨word,valueEq,_,hol,_,_,bound⟩ := counted_scalar_return_invert (executableState branchingHOL)
    (exactState branchingHOL) (source_related _) (source_ranged _) words (.const 7)
    (Scalar.const (scope := []) _) (by simp [ExpByteRanged]) (.word 7) (fun _ => none)
    context primitive handler [] 1 2 run
  cases valueEq
  exact ⟨by simpa [expToHOL] using hol,by simpa [expToHOL] using bound⟩
/-- A populated local also witnesses the assignment inversion premises. -/
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ value,
      (setVarHOLFinite (ofString "x") (.val (.word 2)) (exactState branchingHOL)).evaluateHOLFiniteState
        (.assign .local (ofString "x") (.const 1)) =
        (none,setVarHOLFinite (ofString "x") (panValueToHOL value)
          (setVarHOLFinite (ofString "x") (.val (.word 2)) (exactState branchingHOL))) := by
  let p := {executableState branchingHOL with locals := updatePanValueMap (executableState branchingHOL).locals "x" (.word 2)}
  let source := setVarHOLFinite (ofString "x") (.val (.word 2)) (exactState branchingHOL)
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have rel : PanSemStateRelExec p source.toExact := by
    simpa [p,source] using (source_related branchingHOL).updateLocals "x" countdown_name_ranged (.word 2)
  have ranged : PanSemStateRelExecRanged p := by
    exact (source_ranged branchingHOL).updateLocals "x" (.word 2) (by simp [PanValueByteRanged])
  have run : evalPanValueFfiProgSteps context primitive handler p.structs [] p.baseAddress p.topAddress
      panSemBitVec64BytesInWord 1 p.locals p.globals p.memory p.ffi (.assign .local "x" (.const 1))
      (memoryAccess := some (panSemBitVec64MemoryAccess p)) =
      some (.normal (updatePanValueMap p.locals "x" (.word 1)) p.globals p.memory p.ffi,2) := by
    simp [p,evalPanValueFfiProgSteps,panValueAssignLocalSteps,evalPanValueExpCountedWith,evalPanValueExpCounted,
      evalPanValueExp,panValueExpStepCost,panValueAssignmentValid,updatePanValueMap,panValueShape,panShapeMatches]
  obtain ⟨value,_,hol,_,_,_⟩ := counted_assign_invert p source rel ranged "x" countdown_name_ranged
    (.const 1) (by simp [ExpByteRanged]) context primitive handler [] 1 2
    (updatePanValueMap p.locals "x" (.word 1)) run
  exact ⟨value,by simpa [source,expToHOL] using hol⟩
/-- A concrete comparison witnesses the condition inversion premises. -/
example :
    @evalHOLExact 64 Unit _ (exactState branchingHOL).toExact
      (fun a => Classical.propDecidable ((exactState branchingHOL).memaddrs a))
      (.cmp .lower (.const 0) (.const 1)) = some (.val (.word 1)) := by
  let p := executableState branchingHOL
  have run : panValueIteCondition p.structs p.baseAddress p.topAddress panSemBitVec64BytesInWord
      p.locals p.globals p.memory (.cmp .lower (.const 0) (.const 1)) (some (panSemBitVec64MemoryAccess p)) = some (1,3) := by
    simp [panValueIteCondition,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,
      panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,
      RiscV.panRiscVMemoryModel,RiscV.panRiscVCmp]
  have result := counted_condition_invert p (exactState branchingHOL) (source_related _) (source_ranged _)
    (.cmp .lower (.const 0) (.const 1)) (by simp [ExpByteRanged]) 1 3 run
  simpa [expToHOL] using result.1
/-- A concrete scalar declaration witnesses the initializer inversion. -/
example : ∃ word,
    (PanValue.word (2 : BitVec 64)) = .word word ∧ 1 = panValueExpStepCost (.const (2 : BitVec 64)) ∧
    @evalHOLExact 64 Unit _ (exactState branchingHOL).toExact
      (fun a => Classical.propDecidable ((exactState branchingHOL).memaddrs a)) (.const 2) = some (.val (.word word)) := by
  let p := executableState branchingHOL
  have words : WordLocals p.locals := by
    simpa [p,executableState,singleEntrySourceProduction,sourceProduction] using wordLocals_empty
  have run : panValueDecAccepted p.structs p.baseAddress p.topAddress panSemBitVec64BytesInWord p.locals p.globals p.memory
      (.const 2) (some (panSemBitVec64MemoryAccess p)) .one = some (.word 2,1) := by
    simp [panValueDecAccepted,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panValueShape,panShapeMatches]
  have result := counted_scalar_initializer_invert p (exactState branchingHOL) (source_related _) (source_ranged _) words
    (.const 2) (Scalar.const (scope := []) _) (by simp [ExpByteRanged]) (.word 2) 1 run
  simpa [expToHOL] using result
/-- The general outcome classification applies to the two-branch loop run. -/
example (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    BasicControl (.returned (executableState (progToHOL branchingLoop)).locals
      (executableState (progToHOL branchingLoop)).globals (executableState (progToHOL branchingLoop)).memory
      (executableState (progToHOL branchingLoop)).ffi [.word 7]) := by
  exact supported_counted_basic context primitive handler (executableState (progToHOL branchingLoop)).structs []
    (executableState (progToHOL branchingLoop)).baseAddress (executableState (progToHOL branchingLoop)).topAddress
    (some (panSemBitVec64MemoryAccess (executableState (progToHOL branchingLoop)))) 7 branchingLoop_supported.1
    _ _ _ _ _ 23 (branchingLoop_source_run context primitive handler)
end SteppedFlapjack.Test
