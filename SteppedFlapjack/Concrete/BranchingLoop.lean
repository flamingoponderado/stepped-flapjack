import SteppedFlapjack.Concrete.CrepCountdown

/-! A supported loop that takes both arms of its conditional. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

/-- The first iteration changes 2 to 1; the second changes 1 to 0. -/
def branchingLoop : Prog (RiscV.Word 64) :=
 .dec "x" .one (.const 2) (.seq (.while (.var .local "x")
  (.ite (.cmp .equal (.var .local "x") (.const 2))
   (.assign .local "x" (.const 1)) (.assign .local "x" (.const 0)))) (.return (.const 7)))

theorem branchingLoop_supported : Supported branchingLoop := by
  constructor
  · exact .decl "x" (.const _) (.seq
      (.while (.local "x" (by simp)) (.ite
        (.cmp .equal (.local "x" (by simp)) (.const _))
        (.assign "x" (by simp) (.const _)) (.assign "x" (by simp) (.const _))))
      (.ret (.const _)))
  · simp [branchingLoop,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4000 in
/-- Both conditional arms execute, and the source evaluator uses exactly 23 steps. -/
theorem branchingLoop_source_run (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
 (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
 evalPanValueFfiProgSteps context primitive handler (executableState (progToHOL branchingLoop)).structs []
 (executableState (progToHOL branchingLoop)).baseAddress (executableState (progToHOL branchingLoop)).topAddress panSemBitVec64BytesInWord 7
 (executableState (progToHOL branchingLoop)).locals (executableState (progToHOL branchingLoop)).globals (executableState (progToHOL branchingLoop)).memory
 (executableState (progToHOL branchingLoop)).ffi branchingLoop
 (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (progToHOL branchingLoop)))) =
 some (.returned (executableState (progToHOL branchingLoop)).locals (executableState (progToHOL branchingLoop)).globals
 (executableState (progToHOL branchingLoop)).memory (executableState (progToHOL branchingLoop)).ffi [.word 7],23) := by
 simp (config := {maxSteps := 1000000}) [branchingLoop,evalPanValueFfiProgSteps,panValueDecAccepted,panValueIteCondition,panValueAssignLocalResult,
 panValueReturnResult,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,executableState,singleEntrySourceProduction,
 panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,panSemWordModel,
 RiscV.panRiscVMemoryModel,RiscV.panRiscVCmp,updatePanValueMap,restorePanValueFfiLocal,
 panShapeMatches,panValueShape,panValueAssignmentValid]
 funext name
 simp [restorePanValueLocal]
/-- The generated body of the declared branching-loop witness. -/
def branchingLoopCrepBody : CrepProgHOL 64 :=
  .dec 1 (.const 2) (.seq (.while (.var 1) (.ite (.cmp .equal (.var 1) (.const 2))
    (.seq (.assign 1 (.const 1)) .skip) (.seq (.assign 1 (.const 0)) .skip))) (.return [.const 7]))

set_option linter.unusedSimpArgs false in
/-- The actual compiler output retains the conditional inside the loop. -/
theorem branchingLoop_crep_code : crepPrograms (progToHOL branchingLoop) =
 [(ofString "main",[],.seq .skip (.call none (entryName (progToHOL branchingLoop)) [])),
  (entryName (progToHOL branchingLoop),[],branchingLoopCrepBody)] := by
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp only [branchingLoop,branchingLoopCrepBody,progToHOL,expToHOL,shapeToHOL]
  simp_crep_code

theorem branchingLoop_simp_program : panSimpProg branchingLoop = branchingLoop := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,branchingLoop]

theorem branchingLoop_simp_source :
    panSimpSourceState branchingLoop (exactState (progToHOL branchingLoop)) = exactState (progToHOL branchingLoop) := by
  simp [panSimpSourceState,branchingLoop_simp_program,exactState,singleEntrySourceTemplate]

theorem branchingLoop_simp_declarations :
    panSimpDeclsHOL (declarations (progToHOL branchingLoop)) = declarations (progToHOL branchingLoop) := by
  simpa [branchingLoop_simp_program] using supported_panSimp_declarations branchingLoop branchingLoop_supported

end SteppedFlapjack.Concrete
