import SteppedFlapjack.Concrete.GlobalStructCountedMachine
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem pairStatementWeight : CrepSteps.statementWeight globalStructActualEntryCrep = 12 := by
  unfold globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq]
  simp [CrepSteps.statementWeight,compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairTableWeight : CrepSteps.codeWeight globalStructCallPrograms = 12 := by
  rw [globalStruct_actualPrograms_eq]
  unfold globalStructActualBody
  rw [globalStructWitness_lowering]
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,globalStructActualInit,globalStruct_actual_initializer_eq,
    compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairSyntaxWeight : callSyntaxCost globalStructActualLoopContext globalStructActualEntryCrep = 31 := by
  unfold globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairCallFactor : callClockFactor globalStructActualLoopContext (globalStructCallPrograms.map (fun row => (row.2.1,row.2.2))) 16 globalStructActualEntryCrep = 390 := by
  rw [globalStruct_actualPrograms_eq]
  unfold globalStructActualBody globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq,globalStructWitness_lowering]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl

private theorem pairOptLimit : globalProgramOptLimit globalStructContext pairCrepContext (progToHOL pairWrapper) pairEntryCrep
    (globalSourcePrograms globalStructProgram) pairEntrySource.clock globalStructActualLoopContext globalStructActualLoopContext .ln = 616746942 := by
  unfold globalProgramOptLimit
  rw [pairEntry_actualCompiled,pairSourcePrograms]
  have sourceClock : pairEntrySource.clock = 16 := rfl
  have crepClock : pairEntryCrep.clock = 16 := rfl
  simp only [sourceClock,crepClock]
  rw [pairStatementWeight,pairTableWeight,pairCallFactor,pairSyntaxWeight,globalStruct_loopCodeWeight]
  change loopVisitWeight (optimiseHOL globalStructActualEntryLoop) + max (loopVisitWeight (optimiseHOL globalStructActualEntryLoop)) (62+2) * (2 * (31 + max 31 (62+2) * (16 + 390 * (max 12 12 * 16 + 1)))) = 616746942
  rw [globalStruct_loopEntryWeight]
  decide

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
theorem pairGeneral_clock_numeric :
  let code := globalSourceCode globalStructProgram
  let bs := globalSourceBitmaps globalStructProgram
  let words := globalSourceWords globalStructProgram
  let limit := globalProgramOptLimit globalStructContext pairCrepContext (progToHOL pairWrapper) pairEntryCrep
    (globalSourcePrograms globalStructProgram) pairEntrySource.clock globalStructActualLoopContext globalStructActualLoopContext .ln
  let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
  let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
  948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    bs code (fixtureStackOracle (fixtureCompilerConfig code)) n = 374713592693268806748 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  dsimp only
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  rw [pairSourceBitmaps,pairSourceCode,pairSourceWords]
  have bitmap : globalStructNativeBitmaps = [4] := globalStruct_nativeBitmap
  rw [bitmap]
  have factor := globalStruct_tickFactor (fixtureCompilerConfig globalStructNativeCode)
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init,pairOptLimit,globalStruct_wordCodeWeight,globalStruct_stackCodeWeight]
  simp [flattenStepFactor]

/-- The named pair source compiles to the bytes run by the initialized machine,
which halts at a numeric clock with the source's I/O events. -/
theorem pairGeneral_namedSource_numeric : ∃ compilerFinal finalMachine finalFfi,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig namedGlobalStructProgram =
      some (fixtureCodeBytes (globalSourceCode globalStructProgram),globalSourceBitmaps globalStructProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode globalStructProgram))) sourceFfi
      374713592693268806748 (configuredMachineState (globalSourceCode globalStructProgram) (globalSourceBitmaps globalStructProgram)) =
        (.halt .success,finalMachine,finalFfi) ∧
    semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram = .terminate .success finalFfi.ioEvents := by
  have safe : fixtureStackSafe (globalSourceCode globalStructProgram) = true := by
    rw [pairSourceCode]
    exact globalStruct_nativeSafe
  have success : (fixtureRemoveLabels (globalSourceCode globalStructProgram)).isSome = true := by
    rw [pairSourceCode]
    exact globalStruct_nativeCompilerFacts.1
  obtain ⟨compilerFinal,compiled⟩ := globalSource_compilerOutputFor namedGlobalStructProgram globalStructProgram
    pairNamed_rawWords safe success
  obtain ⟨machine,ffi,run,semantics⟩ := pairGeneral_namedSource
  refine ⟨compilerFinal,machine,ffi,compiled,?_,semantics⟩
  rw [← pairGeneral_clock_numeric]
  exact run

end SteppedFlapjack.Concrete
