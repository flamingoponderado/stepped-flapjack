import SteppedFlapjack.PanToCrepSteps.CountdownAllocationMoves
import SteppedFlapjack.RegAllocSteps.ListInitializer

/-! Row-parameterized staged coloring for executable register allocation. -/
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc SteppedFlapjack.RegAllocSteps
open SteppedFlapjack.PanToCrepSteps

namespace SteppedFlapjack.PanToCrepSteps.RowColoring
variable (row : Nat × Nat × WordLangProgHOL (BitVec 64))
def input := countdownPreAllocation row.2.1 row.2.2
def tree := WordAlloc.getClashTree (input row) []
def moves := (WordAlloc.getHeuristics 3 row.1 (input row)).1
def bij := cakeMkBij (nativeClashTreeToProduction (tree row))
def rendered := nativeClashTreeToProduction (tree row)
def forced := WordAlloc.getForced riscvConfig (input row) []
def stackOnly := (sptToAList (WordAlloc.getStackOnly (input row))).map Prod.fst
def state := listDecoderInit (bij row) (rendered row) (forced row) (stackOnly row)
def limit := riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)
def decoded := (moves row).map (cakeUpdateMove (CakeAlloc.spDefault (bij row).toAllocator))
def admitted := filterReversed (fun (m : Nat × (Nat × Nat)) => cakeFullConsistencyOk (state row) limit m.2.1 m.2.2) (decoded row)
def start := cakeInitAlloc1Heu (admitted row) limit (state row)
def costs := (WordAlloc.getHeuristics 3 row.1 (input row)).2.map (fun c => cakeSpillCostMap (bij row).nextNode (sptToAList c))
def allocated := cakeRptDoStep (costs row) limit (start row).1 (start row).2
def prefs := cakeResortMovesSp (cakeMovesToSp (decoded row) (CakeNodeMap.ofSize (bij row).nextNode))
def coloredA := cakeAssignAtemps limit (allocated row).stack (fun s n ks => cakeBiasedPref s (prefs row) n ks) (allocated row)
def colored := cakeAssignStemps limit (fun s n bads => cakeNegBiasedPref s limit (prefs row) n bads) (coloredA row)
/-- A successful staged run determines the executable allocator result. -/
theorem graphAllocation_exact
    (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (cols : List (Nat × Nat))
    (guard : countdownAllocatorGuard row = true)
    (failure : (colored row).failure = none)
    (extract : cakeExtractColor (colored row) (bij row).toAllocator = cols) :
    regAllocExecutable .IRC (WordAlloc.getHeuristics 3 row.1 (input row)).2
      limit (moves row) (tree row) (forced row) (WordAlloc.getStackOnly (input row)) =
      .success (sptFromAList cols) := by
  have colors : listDecoderColor .irc (costs row) limit (moves row)
      (rendered row) (forced row) (stackOnly row) = some cols := by
    change (if (colored row).failure.isSome then none else
      some (cakeExtractColor (colored row) (bij row).toAllocator)) = _
    rw [failure]
    simp only [Option.isSome_none,Bool.false_eq_true,if_false,extract]
  rw [listDecoderColor_eq] at colors
  have accepted : nativeRegAllocInputGuard (WordAlloc.getHeuristics 3 row.1 (input row)).2
      (tree row) (forced row) (WordAlloc.getStackOnly (input row)) = true := by
    cases row with | mk name rest => cases rest with | mk arity prog => exact guard
  unfold regAllocExecutable
  rw [accepted]
  change (match cakeDoRegAlloc .irc (costs row) limit (moves row)
      (rendered row) (forced row) (stackOnly row) with
    | some result => Translator.Monadic.MonadBase.Exc.success (sptFromAList result)
    | none => _) = _
  rw [colors]

/-- The actual single-function compiler applies the staged coloring. -/
theorem compiled_exact
    (row : Nat × Nat × WordLangProgHOL (BitVec 64)) (cols : List (Nat × Nat))
    (guard : countdownAllocatorGuard row = true)
    (failure : (colored row).failure = none)
    (extract : cakeExtractColor (colored row) (bij row).toAllocator = cols) :
    WordToWord.fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith limit 3 riscvConfig (row,none) =
      (row.1,row.2.1,WordRemove.removeMustTerminate
        (WordAlloc.applyColour (WordAlloc.totalColour (sptFromAList cols)) (input row))) := by
  have hcolor : WordToWord.selectRegAllocWith regAllocExecutable 3
      (WordAlloc.getHeuristics 3 row.1 (input row)).2 limit (moves row) (tree row) (forced row)
      (WordAlloc.getStackOnly (input row)) = .success (sptFromAList cols) := by
    simpa only [WordToWord.selectRegAllocWith,show ¬ 4 ≤ 3 by decide,if_false,
      show ¬ 3 ≤ 1 by decide] using graphAllocation_exact row cols guard failure extract
  cases hrow : row with
  | mk name rest =>
    cases rest with
    | mk arity prog =>
      simp only [hrow,moves,tree,forced,limit] at hcolor ⊢
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
      simp only [input] at hcolor ⊢
      rw [hcolor]

end SteppedFlapjack.PanToCrepSteps.RowColoring
