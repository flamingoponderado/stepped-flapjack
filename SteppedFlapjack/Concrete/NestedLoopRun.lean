import SteppedFlapjack.Concrete.NestedCrepLoop
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

theorem nestedCall_loop_run :
    evaluate nestedLoopCode64 nestedLoopState =
      (some (.result [.word 7]),{nestedLoopState with locals := .ln,clock := 0}) := by
  apply nestedLoop_entry_run nestedLoopState
  · simp [nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,nestedLoopTable]
  · rfl

open SteppedFlapjack.LoopSteps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_leaf_count (s : LoopSemStateFiniteExact 64 Unit) : steps nestedLoopCode67 s = 8 := by
  simp [nestedLoopCode67,steps_mark,steps_seq,steps_leaf,evaluate,eval,
    LoopSemStateFiniteExact.setVar, LoopSemStateFiniteExact.getVars,
    sptLookup_sptInsert_same,LoopSemStateFiniteExact.callEnv]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_middle_count (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock ≠ 0) : steps nestedLoopCode66 s = 12 := by
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  have found : findCode (some 67) [] s.code = some (.ln,nestedLoopCode67) := by
    simp [findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,empty]
  have call := steps_call_tail (some 67) [] s [] .ln nestedLoopCode67 (by rfl) found clock
  have run : ∃ t, evaluate (.mark (.call none (some 67) [] none) : HolLoopProg 64) s = (some (.result [.word 7]),t) := by
    refine ⟨callEnv [] (setVar 1 (.word 7) {decClock s with locals := .ln}), ?_⟩
    simp [evaluate,found,clock,nestedLoopCode67,evaluate_seq,eval,LoopSemStateFiniteExact.setVar,LoopSemStateFiniteExact.getVars,sptLookup_sptInsert_same,LoopSemStateFiniteExact.callEnv]
  obtain ⟨t, run⟩ := run
  simp [nestedLoopCode66,steps_mark,steps_seq,call,nestedLoop_leaf_count,run]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_returning_count (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 3) :
  steps (.call (some ([1],.ln)) (some 66) []
    (some (2,.mark (.raise 2),.mark .skip,nestedLoopLive1))) s = 15 := by
  let cut : LoopSemStateFiniteExact 64 Unit := {s with locals := .ln, clock := 2}
  let called : LoopSemStateFiniteExact 64 Unit := {cut with locals := .ln}
  let post := LoopSemStateFiniteExact.callEnv [] (setVar 1 (.word 7) {decClock called with locals := .ln})
  have interEmpty : sptInter s.locals (.ln : NumSet) = .ln := by cases s.locals <;> simp [sptInter]
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  have cutRun : cutRes .ln (none,s) = (none,cut) := by
    simp [cutRes,cutState,sptSubsetLive,clock,cut,decClock,interEmpty]
  have found : findCode (some 66) [] s.code = some (.ln,nestedLoopCode66) := by
    simp [findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,empty]
  have calledCode : called.code = nestedLoopTable := by simpa [called,cut] using code
  have calledClock : called.clock ≠ 0 := by simp [called,cut]
  have run : evaluate nestedLoopCode66 {cut with locals := .ln} = (some (.result [.word 7]),post) := by
    exact nestedLoop_middle_run called calledCode calledClock
  have count := nestedLoop_middle_count called calledCode calledClock
  have call := steps_call_returning (some 66) [] [1] .ln (some (2,.mark (.raise 2),.mark .skip,nestedLoopLive1)) s cut post [] .ln nestedLoopCode66 (some (.result [.word 7])) (by rfl) found (by simp) cutRun run
  simp [call,steps_mark,steps_leaf,count,called]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_main_count (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 3) :
  steps nestedLoopCode65 s = 38 := by
  have call := nestedLoop_returning_count s code clock
  have run := nestedLoop_returning_run s code clock
  simp [nestedLoopCode65,steps_mark,steps_seq,steps_leaf,evaluate_seq,evaluate,call,run,eval,
    LoopSemStateFiniteExact.setVar,LoopSemStateFiniteExact.getVars,
    sptLookup_sptInsert_same,LoopSemStateFiniteExact.callEnv]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem nestedLoop_entry_count (s : LoopSemStateFiniteExact 64 Unit) (code : s.code = nestedLoopTable) (clock : s.clock = 4) :
  steps nestedLoopCode64 s = 46 := by
  let entry : LoopSemStateFiniteExact 64 Unit := {decClock s with locals := .ln}
  have entryCode : entry.code = nestedLoopTable := by simpa [entry,decClock] using code
  have entryClock : entry.clock = 3 := by simp [entry,decClock,clock]
  have run := nestedLoop_main_run entry entryCode entryClock
  have count := nestedLoop_main_count entry entryCode entryClock
  have empty : sptFromAList ([] : List (Nat × WordLocW 64)) = .ln := rfl
  have found : findCode (some 65) [] s.code = some (.ln,nestedLoopCode65) := by
    simp [findCode,code,nestedLoopTable,sptLookup_sptFromAList,sptAListLookup,empty]
  have nonzero : s.clock ≠ 0 := by simp [clock]
  have call := steps_call_tail (some 65) [] s [] .ln nestedLoopCode65 (by rfl) found nonzero
  have callRun : evaluate (.call none (some 65) [] none : HolLoopProg 64) s =
      (some (.result [.word 7]),{s with locals := .ln,clock := 0}) := by
    simp [entry,decClock,clock] at run
    simp [evaluate,found,decClock,clock,run]
  simp [nestedLoopCode64,steps_mark,steps_seq,steps_leaf,evaluate,call,callRun,count,entry]

/-- The optimized Loop witness visits exactly 46 evaluator nodes. -/
theorem nestedCall_loop_steps : steps nestedLoopCode64 nestedLoopState = 46 := by
  apply nestedLoop_entry_count nestedLoopState
  · simp [nestedLoopState,concreteDeclLoopState,nestedCall_loop_code,nestedLoopTable]
  · rfl

end SteppedFlapjack.Concrete
