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
  have result := counted_return_invert (executableState branchingHOL) (exactState branchingHOL)
    (source_related _) (source_ranged _) (.const 7) (by simp [ExpByteRanged]) 7 context primitive handler [] 1 2 run
  exact ⟨by simpa [expToHOL] using result.1,by simpa [expToHOL] using result.2.2.2⟩
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
end SteppedFlapjack.Test
