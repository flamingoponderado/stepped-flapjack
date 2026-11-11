import SteppedFlapjack.LoopToWordSteps.WholeCallProgram
import SteppedFlapjack.Concrete.NestedCrepLoop
import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode
/-! Bottom-up execution of the actual optimized Loop witness. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_leaf_run (s : LoopSemStateFiniteExact 64 Unit) :
  evaluate nestedLoopCode67 s = (some (.result [.word 7]), callEnv [] (setVar 1 (.word 7) s)) := by
  simp [nestedLoopCode67,evaluate_seq,evaluate,eval,LoopSemStateFiniteExact.setVar,
    LoopSemStateFiniteExact.getVars,sptLookup_sptInsert_same,LoopSemStateFiniteExact.callEnv]

def nestedLoopTable : Spt (List Nat × HolLoopProg 64) := sptFromAList [(64,[],nestedLoopCode64),(65,[],nestedLoopCode65),(66,[],nestedLoopCode66),(67,[],nestedLoopCode67)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The optimized Loop code table has control weight 26. -/
theorem nestedCall_loop_codeWeight : SteppedFlapjack.LoopLiveSteps.loopCodeWeight nestedLoopTable = 26 := by
  with_unfolding_all rfl

open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordSteps

/-- The actual Loop-to-Word table for the four-function nested-call witness. -/
def nestedWordTable := sptFromAList (loopToWordCompileHOL [(64,[],nestedLoopCode64),(65,[],nestedLoopCode65),(66,[],nestedLoopCode66),(67,[],nestedLoopCode67)])
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The nested-call Word table has concrete control weight 17. -/
theorem nestedCall_word_codeWeight : wordCodeWeight nestedWordTable = 17 := by
  with_unfolding_all rfl

/-- Starting any function in the witness table takes at most 17 visits per clock tick, plus the call. -/
theorem nestedCall_word_start_bound {C F : Type} (s : WordSemStateFiniteExact 64 C F)
    (code : s.code = nestedWordTable) (start : Nat) :
    steps (.call none (some start) [0] none) s ≤ 1 + 17 * s.clock := by
  have mt : WordProps.noMtCode s.code := by
    rw [code]
    exact LoopToWord.loop_compile_no_mt_code _
  have ni : WordProps.noInstallCode s.code := by
    rw [code]
    exact LoopToWord.loop_compile_no_install_code _
  have bound := wordTable_clock_bound (.call none (some start) [0] none) s rfl rfl mt ni
  simpa [wordControlWeight,code,nestedCall_word_codeWeight] using bound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_middle_run (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock ≠ 0) :
  evaluate nestedLoopCode66 s = (some (.result [.word 7]),
    LoopSemStateFiniteExact.callEnv [] (setVar 1 (.word 7) {decClock s with locals := .ln})) := by
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  rw [nestedLoopCode66,evaluate,evaluate_seq,evaluate,evaluate]
  simp [empty,LoopSemStateFiniteExact.getVars,findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,clock,nestedLoop_leaf_run]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_returning_run (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 3) :
  evaluate (.call (some ([1],.ln)) (some 66) []
    (some (2,.mark (.raise 2),.mark .skip,nestedLoopLive1))) s =
      (none,{s with locals := sptInsert 1 (.word 7) .ln, clock := 0}) := by
  let cut : LoopSemStateFiniteExact 64 Unit := {s with locals := .ln, clock := 2}
  let called : LoopSemStateFiniteExact 64 Unit := {cut with locals := .ln}
  let post := LoopSemStateFiniteExact.callEnv [] (setVar 1 (.word 7) {decClock called with locals := .ln})
  have interEmpty : sptInter s.locals (.ln : NumSet) = .ln := by cases s.locals <;> simp [sptInter]
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  have subset : ∀ key, (sptLookup key (sptInsert 1 () .ln)).isSome = true →
      (sptLookup key (sptInsert 1 (.word 7 : WordLocW 64) .ln)).isSome = true := by
    intro key present
    by_cases same : key = 1
    · subst key
      simp [sptLookup_sptInsert_same]
    · have missing := sptLookup_sptInsert_ne 1 key () (Spt.ln : Spt Unit) same
      simp [sptLookup] at missing
      simp [missing] at present
  have cutRun : cutRes .ln (none,s) = (none,cut) := by
    simp [cutRes,cutState,sptSubsetLive,clock,cut,decClock,interEmpty]
  have found : findCode (some 66) [] s.code = some (.ln,nestedLoopCode66) := by
    simp [findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,empty]
  have calledCode : called.code = nestedLoopTable := by simpa [called,cut] using code
  have calledClock : called.clock ≠ 0 := by simp [called,cut]
  have run : evaluate nestedLoopCode66 {cut with locals := .ln} = (some (.result [.word 7]),post) := by
    exact nestedLoop_middle_run called calledCode calledClock
  have call := SteppedFlapjack.LoopSteps.evaluate_call_returning_success
    (some 66) [] [1] .ln nestedLoopLive1 2 (.mark (.raise 2)) (.mark .skip) s cut post [] [.word 7] .ln nestedLoopCode66
    (by rfl) found (by simp) cutRun run (by rfl)
  rw [call,evaluate,evaluate]
  simp [cutRes,cutState,sptSubsetLive,sptInter,nestedLoopLive1,
    LoopSemStateFiniteExact.setVars,post,called,cut,decClock,
    LoopSemStateFiniteExact.callEnv,LoopSemStateFiniteExact.setVar,sptAlistInsert,sptInsert,sptLookup,sptMem,sptDomain,sptMkBN]
  split
  · simp_all
  · rename_i out heq
    simp_all
    subst out
    rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_main_run (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 3) :
  evaluate nestedLoopCode65 s = (some (.result [.word 7]), {s with locals := .ln, clock := 0}) := by
  have call := nestedLoop_returning_run s code clock
  have skipRun : evaluate (.mark .skip : HolLoopProg 64) s = (none,s) := by simp [evaluate]
  rw [nestedLoopCode65,evaluate,evaluate_seq,skipRun]
  simp only
  rw [evaluate,evaluate_seq,skipRun]
  simp only
  rw [evaluate,evaluate_seq,evaluate,evaluate_seq,evaluate,call]
  simp only
  simp [evaluate_seq,evaluate,eval,LoopSemStateFiniteExact.setVar,
    LoopSemStateFiniteExact.getVars,sptLookup_sptInsert_same,LoopSemStateFiniteExact.callEnv]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_entry_run (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 4) :
  evaluate nestedLoopCode64 s = (some (.result [.word 7]), {s with locals := .ln, clock := 0}) := by
  let entry : LoopSemStateFiniteExact 64 Unit := {decClock s with locals := .ln}
  have entryCode : entry.code = nestedLoopTable := by simpa [entry,decClock] using code
  have entryClock : entry.clock = 3 := by simp [entry,decClock,clock]
  have run := nestedLoop_main_run entry entryCode entryClock
  have run' : evaluate nestedLoopCode65 {s with locals := .ln,clock := 3,code := nestedLoopTable} =
      (some (.result [.word 7]),{s with locals := .ln,clock := 0,code := nestedLoopTable}) := by
    simpa [entry,decClock,clock,code] using run
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  have skipRun : evaluate (.mark .skip : HolLoopProg 64) s = (none,s) := by simp [evaluate]
  rw [nestedLoopCode64,evaluate,evaluate_seq,skipRun]
  simp only
  rw [evaluate,evaluate_seq,evaluate,evaluate]
  simp [LoopSemStateFiniteExact.getVars,findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,clock,decClock,empty]
  simp only [nestedLoopTable] at run'
  rw [run']
  rfl

/-- The actual optimized Loop entry returns seven from the concrete source fixture. -/
noncomputable def nestedLoopState : LoopSemStateFiniteExact 64 Unit :=
  concreteDeclLoopState riscvConfig.isa nestedCrepState nestedCallCrepPrograms

theorem nestedCall_loop_run (memory : BitVec 64 → WordLocW 64) :
    evaluate nestedLoopCode64 {nestedLoopState with memory := memory} =
      (some (.result [.word 7]),{{nestedLoopState with memory := memory} with locals := .ln,clock := 3}) := by
  let base : LoopSemStateFiniteExact 64 Unit := {nestedLoopState with memory := memory, clock := 4}
  have code : base.code = nestedLoopTable := by
    simp [base,nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,nestedLoopTable]
  have run := nestedLoop_entry_run base code rfl
  have lifted := evaluate_add_clock_eq nestedLoopCode64 base (some (.result [.word 7]))
    {base with locals := .ln,clock := 0} 3 run (by simp)
  simpa [base,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate] using lifted

open SteppedFlapjack.LoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepToLoopSteps

private theorem nestedTable_supported : LoopTableSupported nestedLoopTable := by
  unfold nestedLoopTable
  rw [← nestedCall_loop_code,nestedCallCrepPrograms]
  exact nestedCall_generated_table_supported

/-- The actual nested-call entry is bounded by the general code-table theorem. -/
theorem nestedCall_loop_steps_bound (memory : BitVec 64 → WordLocW 64) :
    steps nestedLoopCode64 {nestedLoopState with memory := memory} ≤ 122 := by
  have codeEq : ({nestedLoopState with memory := memory} : LoopSemStateFiniteExact 64 Unit).code = nestedLoopTable := by
    simp [nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,nestedLoopTable]
  have found : sptLookup 64 nestedLoopTable = some ([],nestedLoopCode64) := by
    simp [nestedLoopTable,sptLookup_sptFromAList,sptAListLookup]
  have bound := loopTable_entry_bound nestedLoopTable 64 [] nestedLoopCode64 {nestedLoopState with memory := memory} codeEq nestedTable_supported found
  rw [nestedCall_loop_codeWeight] at bound
  rw [nestedCall_loop_run memory] at bound
  have clock : ({nestedLoopState with memory := memory} : LoopSemStateFiniteExact 64 Unit).clock = 7 := rfl
  rw [clock] at bound
  simp only at bound
  have entryWeight : loopVisitWeight nestedLoopCode64 = 10 := by with_unfolding_all rfl
  rw [entryWeight] at bound
  omega

/-- The actual nested-call entry has the full Loop-to-Word sixfold
simulation, including both reached callees. -/
theorem nestedCall_loopToWord_with_steps {C : Type} :
    SteppedFlapjack.LoopToWordSteps.SixBoundPropertyAt C nestedLoopCode64 nestedLoopState := by
  apply SteppedFlapjack.LoopToWordSteps.loopTable_entry_correct_with_steps nestedLoopTable 64 []
    nestedLoopCode64 nestedLoopState
  · simp [nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,nestedLoopTable]
  · exact nestedTable_supported
  · simp [nestedLoopTable,sptLookup_sptFromAList,sptAListLookup]

open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps
def nestedPanContext := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL
  (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) 0
  (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))
def nestedLoopContext := mkCtxtExact riscvConfig.isa (makeVmapExact [])
  (crepToLoopMakeFuncsExactExecutable nestedCallCrepPrograms) 0
def nestedCrepBody : CrepProgHOL 64 := compileProgExactHOLW nestedPanContext (.seq .skip (.call none (ofString "main'") []))
def nestedCrepLimit := 4 * nestedSourceEntryLimit
def nestedLoopBudget := callClockFactor nestedLoopContext
  (nestedCallCrepPrograms.map (fun row => (row.2.1,row.2.2))) 7 nestedCrepBody * (nestedCrepLimit + 1)
def nestedLoopBound := callSyntaxCost nestedLoopContext nestedCrepBody +
  max (callSyntaxCost nestedLoopContext nestedCrepBody) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms))+2) * (7+nestedLoopBudget)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The counted source bound supplies a concrete clock and visit bound for the generated Loop body. -/
theorem nestedCounted_crepToLoop : ∃ final, evaluate (compileHOLExact nestedLoopContext .ln nestedCrepBody)
      {nestedLoopState with clock := nestedLoopState.clock+nestedLoopBudget} = (some (.result [.word 7]),final) ∧ final.ffi = sourceFfi ∧
    LoopSteps.steps (compileHOLExact nestedLoopContext .ln nestedCrepBody)
      {nestedLoopState with clock := nestedLoopState.clock+nestedLoopBudget} ≤ nestedLoopBound := by
  let decls := compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")
  let p : ProgHOL 64 := .seq .skip (.call none (ofString "main'") [])
  have shape : CallFrontend nestedPanContext p := .seq (.base .skip) (.tail (by simp))
  have sources := callFrontend_declaration_sources decls nestedCall_declaration_shapes
  obtain ⟨crepFinal,run,ffi,bound⟩ := nestedCall_sourceToCrep_bound
  have compileEq : nestedCrepBody = .seq .skip (.call none (ofString "main'") []) := by
    simp [nestedCrepBody,nestedPanContext,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  have sourceCode : nestedCrepState.code = alistToFmapCodeExact nestedCallCrepPrograms := rfl
  have relations := concreteDecl_crepLoop_relations riscvConfig.isa nestedCrepState nestedCallCrepPrograms rfl
  have locals : crepToLoopLocalsRelExact nestedLoopContext .ln nestedCrepState.locals nestedLoopState.locals := by
    apply empty_crepLoop_locals
    rfl
  have code : crepToLoopCodeRelExact nestedLoopContext nestedCrepState.code nestedLoopState.code := by
    rw [sourceCode]
    simpa [nestedLoopContext,nestedLoopState,concreteDeclLoopState] using nestedCall_loop_code_relation
  have table : LoopTableSupported nestedLoopState.code := by
    simpa only [nestedLoopState,concreteDeclLoopState,nestedCallCrepPrograms] using nestedCall_generated_table_supported
  have span := callFrontend_wholeVisits_explicit nestedPanContext p shape nestedCallCrepPrograms
    (by
      rw [nestedCallCrepPrograms,compileProgDeclsHOLW,nestedCall_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil]
      exact sources) nestedLoopContext nestedLoopContext .ln
    nestedCrepState crepFinal (some (.return [.word 7])) nestedLoopState sourceCode
    (by change evalCrepSemHOLProgExact nestedCrepState nestedCrepBody = _; rw [compileEq]; exact run) (by simp) (by simp) nestedCrepLimit
    (by change CrepSteps.steps nestedCrepBody nestedCrepState ≤ 4 * nestedSourceEntryLimit; rw [compileEq]; exact bound)
    relations.1 relations.2.1 relations.2.2 code table locals
  obtain ⟨final,ev,visits,stateRel,_,_,_,_⟩ := span
  refine ⟨final,?_,?_,?_⟩
  · simpa [p,wlabWlocExact,Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop,nestedLoopBudget,nestedCrepLimit,nestedCrepBody,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate] using ev
  · exact stateRel.2.2.2.2.1.symm.trans ffi
  · simpa [p,nestedLoopBound,nestedLoopBudget,nestedCrepLimit,nestedCrepBody,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate] using visits

def nestedOptimizedLoopBody := optimiseHOL (compileHOLExact nestedLoopContext .ln nestedCrepBody)
def nestedOptimizedLoopBound :=
  loopVisitWeight nestedOptimizedLoopBody +
    max (loopVisitWeight nestedOptimizedLoopBody)
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)) + 2) * (2 * nestedLoopBound)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedOptimizedLoopBody_eq : nestedOptimizedLoopBody = nestedLoopCode64 := by
  have head := congrArg List.head? nestedCall_loop_code
  have crep : nestedCrepBody = .seq .skip (.call none (ofString "main'") []) := by
    simp [nestedCrepBody,nestedPanContext,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList]
  rw [nestedOptimizedLoopBody,crep,nestedLoopContext]
  rw [nestedCallCrepPrograms,nestedCall_crep_code] at head
  simp only [compileProgHOLExact, List.length_cons, List.length_nil] at head
  norm_num only [show List.range 4 = [0,1,2,3] by decide, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.head?_cons, Nat.reduceAdd, Nat.reduceSub, List.length_nil, List.range_zero, compFuncHOLExact, listToNumSetHOLExact, crepSimpProgHOL] at head
  simp only [firstLoopName,Nat.zero_add,crepSimpProgHOL] at head
  rw [nestedCallCrepPrograms,nestedCall_crep_code]
  simpa only [Option.some.injEq,Prod.mk.injEq,true_and] using head


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The counted source-derived visit bound survives the actual Loop optimizer. -/
theorem nestedCounted_optimizedLoop (memory : BitVec 64 → WordLocW 64) : ∃ final, evaluate nestedLoopCode64
      {nestedLoopState with memory := memory, clock := nestedLoopState.clock+nestedLoopBudget} = (some (.result [.word 7]),final) ∧
    final.ffi = sourceFfi ∧ LoopSteps.steps nestedLoopCode64
      {nestedLoopState with memory := memory, clock := nestedLoopState.clock+nestedLoopBudget} ≤ nestedOptimizedLoopBound := by
  rw [← nestedOptimizedLoopBody_eq]
  obtain ⟨final,run,ffi,visits⟩ := nestedCounted_crepToLoop
  let source := {nestedLoopState with clock := nestedLoopState.clock+nestedLoopBudget}
  let body := compileHOLExact nestedLoopContext .ln nestedCrepBody
  have panShape : CallFrontend nestedPanContext (.seq .skip (.call none (ofString "main'") [])) :=
    .seq (.base .skip) (.tail (by simp))
  have shape : SimpleLoopSequenceSource body := by
    exact callFrontend_compiled_loopShape panShape nestedLoopContext .ln
  have table : LoopTableSupported source.code := by
    simpa only [source,nestedLoopState,concreteDeclLoopState,nestedCallCrepPrograms] using nestedCall_generated_table_supported
  have optRun : evaluate (optimiseHOL body) source = (some (.result [.word 7]),final) := by
    apply optimise_correct
    exact ⟨run,by simp,by simp,by simp,by simp⟩
  have originalLow := nestedCall_loop_run nestedLoopState.memory
  have originalLift := evaluate_add_clock_eq nestedLoopCode64 {nestedLoopState with memory := nestedLoopState.memory}
    (some (.result [.word 7])) {{nestedLoopState with memory := nestedLoopState.memory} with locals := .ln,clock := 3}
    nestedLoopBudget originalLow (by simp)
  have origRun : evaluate nestedLoopCode64 source =
      (some (.result [.word 7]),{nestedLoopState with locals := .ln,clock := 3+nestedLoopBudget}) := by
    simpa [source,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate] using originalLift
  have origOpt : evaluate nestedLoopCode64 source = (some (.result [.word 7]),final) := by
    change evaluate nestedOptimizedLoopBody source = _ at optRun
    rw [nestedOptimizedLoopBody_eq] at optRun
    exact optRun
  have sameFinal := (Prod.mk.inj (origOpt.symm.trans origRun)).2
  have finalClock : final.clock = 3+nestedLoopBudget := by
    simpa using congrArg (fun s : LoopSemStateFiniteExact 64 Unit => s.clock) sameFinal
  have lowRun := nestedCall_loop_run memory
  have lifted := evaluate_add_clock_eq nestedLoopCode64 {nestedLoopState with memory := memory}
    (some (.result [.word 7])) {{nestedLoopState with memory := memory} with locals := .ln,clock := 3}
    nestedLoopBudget lowRun (by simp)
  let target := {nestedLoopState with memory := memory,clock := nestedLoopState.clock+nestedLoopBudget}
  let targetFinal := {nestedLoopState with memory := memory,locals := .ln,clock := 3+nestedLoopBudget}
  have targetRun : evaluate nestedLoopCode64 target = (some (.result [.word 7]),targetFinal) := by
    simpa [target,targetFinal,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate] using lifted
  let K := max (loopVisitWeight (optimiseHOL body)) (loopCodeWeight target.code + 2)
  have targetTable : LoopTableSupported target.code := by simpa [target,source] using table
  have optimized := simpleSequence_global_bound (optimiseHOL body) target K (optimise_simpleSequence shape)
    targetTable (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have consumed := simpleSequence_global_consumed body source shape table
  rw [run] at consumed
  have targetRun' : evaluate (optimiseHOL body) target = (some (.result [.word 7]),targetFinal) := by
    change evaluate nestedOptimizedLoopBody target = _
    rw [nestedOptimizedLoopBody_eq]
    exact targetRun
  rw [targetRun'] at optimized
  have clockEq : target.clock - targetFinal.clock = source.clock - final.clock := by
    simp [target,targetFinal,source,finalClock]
  rw [clockEq] at optimized
  have consumption : source.clock - final.clock ≤ 2 * nestedLoopBound :=
    consumed.trans (Nat.mul_le_mul_left 2 visits)
  have scaled := Nat.mul_le_mul_left K consumption
  have finalBound := optimized.trans (Nat.add_le_add_left scaled (loopVisitWeight (optimiseHOL body)))
  refine ⟨targetFinal,?_,?_,?_⟩
  · simpa [nestedOptimizedLoopBody_eq,body,target] using targetRun
  · simp [targetFinal,nestedLoopState,concreteDeclLoopState,nestedCrepState,concreteDeclCrepState,sourceTemplate]
  · simpa [nestedOptimizedLoopBound,nestedOptimizedLoopBody,K,body,target,nestedLoopState,concreteDeclLoopState] using finalBound


end SteppedFlapjack.Concrete
