import SteppedFlapjack.PanToCrepSteps.CountdownWordLiteral
import SteppedFlapjack.RegAllocSteps.GuardSuccess

/-! Successful allocation for the actual zero-count loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc SteppedFlapjack.RegAllocSteps

/-- The loop row of the proved zero-count Word program. -/
def countdownZeroLoopRow : Nat × Nat × WordLangProgHOL (BitVec 64) :=
  (countdownWordLiteral 0 0).get ⟨1, by decide⟩

/-- The exact program passed to register allocation after the earlier Word
passes for the zero-count loop. -/
def countdownZeroAllocInput : WordLangProgHOL (BitVec 64) :=
  countdownPreAllocation countdownZeroLoopRow.2.1 countdownZeroLoopRow.2.2

/-- The loop row really comes from the original Pancake compiler. -/
theorem countdownZeroLoopRow_from_compiler :
    (panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64)))))))).drop 1 = [countdownZeroLoopRow] := by
  rw [countdownWordLiteral_zero_eq]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual graph-coloring call for the zero-count loop succeeds. -/
theorem countdownZero_graphAllocation_success :
    ∃ coloring, regAllocExecutable .IRC
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).2
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).1
      (WordAlloc.getClashTree countdownZeroAllocInput [])
      (WordAlloc.getForced riscvConfig countdownZeroAllocInput [])
      (WordAlloc.getStackOnly countdownZeroAllocInput) = .success coloring := by
  apply executable_success_of_guard
  have guard := countdown_zero_allocator_guard
  rw [countdownZeroLoopRow_from_compiler] at guard
  simpa only [List.map_cons,List.map_nil,List.cons.injEq,true_and,and_true,countdownAllocatorGuard,
    countdownZeroAllocInput] using guard

/-- The actual Word compiler selects that successful IRC allocation. -/
theorem countdownZero_selectedAllocation_success :
    ∃ coloring, WordToWord.selectRegAllocWith regAllocExecutable 3
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).2
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).1
      (WordAlloc.getClashTree countdownZeroAllocInput [])
      (WordAlloc.getForced riscvConfig countdownZeroAllocInput [])
      (WordAlloc.getStackOnly countdownZeroAllocInput) = .success coloring := by
  simpa only [WordToWord.selectRegAllocWith,show ¬ 4 ≤ 3 by decide,if_false,
    show ¬ 3 ≤ 1 by decide] using countdownZero_graphAllocation_success


set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Both functions emitted by the zero-count frontend pass the checked graph
allocator guard. -/
theorem countdownZero_all_allocator_guards :
    ∀ row ∈ panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))), countdownAllocatorGuard row = true := by
  rw [countdownWordLiteral_zero_eq]
  intro row member
  simp only [countdownWordLiteral,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> with_unfolding_all rfl

/-- Graph allocation succeeds for every Word function emitted by the actual
zero-count Pancake frontend. -/
theorem countdownZero_all_graphAllocations_success :
    ∀ row ∈ panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))),
    let prog := countdownPreAllocation row.2.1 row.2.2
    ∃ coloring, regAllocExecutable .IRC (WordAlloc.getHeuristics 3 row.1 prog).2
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
      (WordAlloc.getHeuristics 3 row.1 prog).1 (WordAlloc.getClashTree prog [])
      (WordAlloc.getForced riscvConfig prog []) (WordAlloc.getStackOnly prog) = .success coloring := by
  intro row member
  apply executable_success_of_guard
  exact countdownZero_all_allocator_guards row member

set_option maxHeartbeats 1000000 in
/-- The loop function emitted by the Word compiler is obtained by applying
its successful computed coloring to the exact pre-allocation program. -/
theorem countdownZero_compiledLoop_has_coloring :
    ∃ coloring, WordToWord.fullCompileSingleWith regAllocExecutable
      riscvConfig.twoRegArith (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
      3 riscvConfig (countdownZeroLoopRow,none) =
      (countdownZeroLoopRow.1,countdownZeroLoopRow.2.1,
        WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour coloring) countdownZeroAllocInput)) := by
  obtain ⟨coloring,hcolor⟩ := countdownZero_selectedAllocation_success
  refine ⟨coloring,?_⟩
  cases hrow : countdownZeroLoopRow with
  | mk name rest =>
    cases rest with
    | mk arity prog =>
      simp only [hrow] at hcolor ⊢
      simp only [WordToWord.fullCompileSingleWith,WordToWord.compileSingleWith,
        WordToWord.wordAllocWith,WordAlloc.oracleColourOk]
      change (_,_, WordRemove.removeMustTerminate
        (match WordToWord.selectRegAllocWith regAllocExecutable 3
          (WordAlloc.getHeuristics 3 name (countdownPreAllocation arity prog)).2
          (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length))
          (WordAlloc.getHeuristics 3 name (countdownPreAllocation arity prog)).1
          (WordAlloc.getClashTree (countdownPreAllocation arity prog) [])
          (WordAlloc.getForced riscvConfig (countdownPreAllocation arity prog) [])
          (WordAlloc.getStackOnly (countdownPreAllocation arity prog)) with
        | .success col => WordAlloc.applyColour (WordAlloc.totalColour col) (countdownPreAllocation arity prog)
        | .failure _ => countdownPreAllocation arity prog)) = _
      rw [show countdownZeroAllocInput = countdownPreAllocation arity prog by simp only [countdownZeroAllocInput,hrow]] at hcolor
      rw [hcolor]
      simp only [countdownZeroAllocInput,hrow]

set_option maxHeartbeats 1000000 in
/-- The actual Word-to-Word compiler output contains the successfully colored
loop, using the empty coloring oracle of the RISC-V backend. -/
theorem countdownZero_wordCompiler_loop_colored :
    ∃ coloring, (WordToWord.compileWith regAllocExecutable countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa
        (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
          (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))))).2.drop 1 =
      [(countdownZeroLoopRow.1,countdownZeroLoopRow.2.1,
        WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour coloring) countdownZeroAllocInput))] := by
  obtain ⟨coloring,hcolor⟩ := countdownZero_compiledLoop_has_coloring
  refine ⟨coloring,?_⟩
  rw [countdownWordLiteral_zero_eq]
  have hwords : countdownWordLiteral 0 0 =
      [(64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),countdownZeroLoopRow] := rfl
  rw [hwords]
  have horacle : countdownRiscVBackend.wordToWordConf.colOracle = [] := rfl
  have halg : countdownRiscVBackend.wordToWordConf.regAlg = 3 := rfl
  simp only [WordToWord.compileWith,horacle,halg]
  change [WordToWord.fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith
    (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) 3 riscvConfig
    (countdownZeroLoopRow,none)] = _
  rw [hcolor]

end SteppedFlapjack.PanToCrepSteps
