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
 simp (config := {maxSteps := 1000000}) [branchingLoop,evalPanValueFfiProgSteps,panValueDecAccepted,panValueIteCondition,panValueAssignLocalSteps,
 panValueReturnSteps,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,executableState,singleEntrySourceProduction,
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

/-- The actual code table selects the calculated branching-loop body. -/
theorem branchingLoop_code_lookup :
    (crepState (progToHOL branchingLoop)).code.lookup (entryName (progToHOL branchingLoop)) =
      some ([],branchingLoopCrepBody) := by
  exact generated_callee_lookup (progToHOL branchingLoop) branchingLoopCrepBody branchingLoop_crep_code

private def loopHOL : ProgHOL 64 := progToHOL branchingLoop

private def loopEntry := exactState loopHOL

private def bodyHOL : ProgHOL 64 := .ite (.cmp .equal (.var .local (ofString "x")) (.const 2))
  (.assign .local (ofString "x") (.const 1)) (.assign .local (ofString "x") (.const 0))

private def s2 := setVarHOLFinite (ofString "x") (.val (.word 2)) loopEntry

private def s1 := setVarHOLFinite (ofString "x") (.val (.word 1)) s2.decClockHOLFinite

private theorem step2 : s2.decClockHOLFinite.evaluateHOLFiniteState bodyHOL = (none,s1) := by
  rw [bodyHOL,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,s2,s1,setVarHOLFinite,
    evaluateHOLFiniteState_assign,isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,
    HolFiniteMapExact.lookup_update, decClockHOLFinite,lookupKvarHOLExact,
    setKvarHOLFinite,FUPDATE]

private def loopStmt : ProgHOL 64 := .while (.var .local (ofString "x")) bodyHOL

private def s0 := setVarHOLFinite (ofString "x") (.val (.word 0)) s1.decClockHOLFinite

private theorem step1 : s1.decClockHOLFinite.evaluateHOLFiniteState bodyHOL = (none,s0) := by
  rw [bodyHOL,evaluateHOLFiniteState_ite]
  simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,s2,s1,s0,setVarHOLFinite,
    evaluateHOLFiniteState_assign,isValidValueHOLFinite,shapeOfHOLExact,shapeEqHOL,
    HolFiniteMapExact.lookup_update,decClockHOLFinite,lookupKvarHOLExact,setKvarHOLFinite,FUPDATE]

private instance : DecidablePred s2.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
private instance : DecidablePred s1.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
private instance : DecidablePred s0.memaddrs := by change DecidablePred ordinaryAddress; infer_instance

private theorem ev2 : @evalHOLFinite 64 Unit _ s2 (fun a => Classical.propDecidable (s2.memaddrs a)) (.var .local (ofString "x")) = some (.val (.word 2)) := by
  rw [evalHOLFinite_eq_toExact]
  simp [evalHOLExact,s2,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
private theorem ev1 : @evalHOLFinite 64 Unit _ s1 (fun a => Classical.propDecidable (s1.memaddrs a)) (.var .local (ofString "x")) = some (.val (.word 1)) := by
  rw [evalHOLFinite_eq_toExact]
  simp [evalHOLExact,s1,s2,setVarHOLFinite,decClockHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
private theorem ev0 : @evalHOLFinite 64 Unit _ s0 (fun a => Classical.propDecidable (s0.memaddrs a)) (.var .local (ofString "x")) = some (.val (.word 0)) := by
  rw [evalHOLFinite_eq_toExact]
  simp [evalHOLExact,s0,s1,s2,setVarHOLFinite,decClockHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

private theorem clk2 : s2.clock ≠ 0 := by
  simp [s2,setVarHOLFinite,loopEntry,exactState,singleEntrySourceTemplate,sourceTemplate]
private theorem clk1 : s1.clock ≠ 0 := by
  simp [s1,s2,setVarHOLFinite,decClockHOLFinite,loopEntry,exactState,singleEntrySourceTemplate,sourceTemplate]

private theorem loopRun : s2.evaluateHOLFiniteState loopStmt = (none,s0) := by
  rw [loopStmt,evaluateHOLFiniteState_while_fixClockRewrite,ev2]
  simp only [ne_eq,clk2,if_false,step2]
  rw [evaluateHOLFiniteState_while_fixClockRewrite,ev1]
  simp only [ne_eq,clk1,if_false,step1]
  rw [evaluateHOLFiniteState_while_fixClockRewrite,ev0]
  simp

private theorem cost2 : controlSteps bodyHOL s2.decClockHOLFinite = 2 := by
  rw [bodyHOL,controlSteps_ite]
  simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,s2,setVarHOLFinite,decClockHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,controlSteps.eq_def]
private theorem cost1 : controlSteps bodyHOL s1.decClockHOLFinite = 2 := by
  rw [bodyHOL,controlSteps_ite]
  simp [evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,s1,s2,setVarHOLFinite,decClockHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,controlSteps.eq_def]

private theorem loopCost : controlSteps loopStmt s2 = 7 := by
  have e2 : @evalHOLExact 64 Unit _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a))
      (.var .local (ofString "x")) = some (.val (.word 2)) := by simpa only [evalHOLFinite_eq_toExact] using ev2
  have e1 : @evalHOLExact 64 Unit _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
      (.var .local (ofString "x")) = some (.val (.word 1)) := by simpa only [evalHOLFinite_eq_toExact] using ev1
  have e0 : @evalHOLExact 64 Unit _ s0.toExact (fun a => Classical.propDecidable (s0.memaddrs a))
      (.var .local (ofString "x")) = some (.val (.word 0)) := by simpa only [evalHOLFinite_eq_toExact] using ev0
  rw [loopStmt,controlSteps_while]
  simp only [e2,ne_eq,clk2,not_false_eq_true,cost2,step2]
  rw [controlSteps_while]
  simp only [e1,ne_eq,clk1,not_false_eq_true,cost1,step1]
  rw [controlSteps_while]
  simp [e0]

private theorem seqRun : s2.evaluateHOLFiniteState (.seq loopStmt (.return (.const 7))) =
    (some (.returned (.val (.word 7))),s0.emptyLocalsHOLFinite) := by
  rw [evaluateHOLFiniteState_seq_line780,loopRun]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]

private theorem loopShape : loopHOL = .dec (ofString "x") .one (.const 2)
    (.seq loopStmt (.return (.const 7))) := by
  simp [loopHOL,branchingLoop,progToHOL,expToHOL,shapeToHOL,loopStmt,bodyHOL]

private theorem sourceRun : ∃ final, loopEntry.evaluateHOLFiniteState loopHOL =
    (some (.returned (.val (.word 7))),final) ∧ controlSteps loopHOL loopEntry ≤ 23 := by
  have run : ∃ final, loopEntry.evaluateHOLFiniteState loopHOL =
      (some (.returned (.val (.word 7))),final) := by
    rw [loopShape]
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change ∃ final, ((s2.evaluateHOLFiniteState (.seq loopStmt (.return (.const 7)))).1,_) = _
    rw [seqRun]
    exact ⟨_,rfl⟩
  obtain ⟨final,run⟩ := run
  refine ⟨final,run,?_⟩
  rw [loopShape]
  rw [controlSteps_dec _ _ _ _ _ (.val (.word 2)) (by simp [evalHOLExact]) (by simp [shapeEqHOL,shapeOfHOLExact])]
  change 1 + controlSteps (.seq loopStmt (.return (.const 7))) s2 ≤ 23
  rw [controlSteps_seq,loopRun]
  simp only [loopCost]
  rw [controlSteps.eq_def]
  dsimp only
  omega

/-- The actual generated entry for the declared branching loop. -/
def branchingLoopCrepEntry : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (progToHOL branchingLoop)) [])

def branchingLoopCalleeContext : PanToCrepContextExact 64 :=
  let caller := frontendContext (progToHOL branchingLoop)
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

/-- The 23-step source execution yields a related generated Crep entry run,
with a bound calculated from its compiled body. -/
theorem branchingLoop_entry_crep :
    ∃ targetFinal,
      evalCrepSemHOLProgExact (crepState (progToHOL branchingLoop)) branchingLoopCrepEntry =
        (some (.return [.word 7]),targetFinal) ∧
      CrepSteps.steps branchingLoopCrepEntry (crepState (progToHOL branchingLoop)) ≤
        1130 := by
  obtain ⟨sourceFinal,run,bound⟩ := sourceRun
  have span := supported_original_entry_crep_return_fixture branchingLoop branchingLoop_supported sourceFinal 7 23 run bound
  have lookup := (supported_callee_relations branchingLoop branchingLoop_supported).1
  have codeEq : compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop) = branchingLoopCrepBody := by
    rw [branchingLoop_code_lookup] at lookup
    exact (Prod.mk.inj (Option.some.inj lookup)).2.symm
  change ∃ final,
    evalCrepSemHOLProgExact (crepState (progToHOL branchingLoop)) branchingLoopCrepEntry =
      (some (.return [.word 7]),final) ∧
    CrepSteps.steps branchingLoopCrepEntry (crepState (progToHOL branchingLoop)) ≤
      3 + sizeOf (compileProgExactHOLW branchingLoopCalleeContext (progToHOL branchingLoop)) * 23 at span
  have size : sizeOf branchingLoopCrepBody = 49 := by decide
  rw [codeEq,size] at span
  simpa using span

end SteppedFlapjack.Concrete
