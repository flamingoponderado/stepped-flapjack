import SteppedFlapjack.PanToCrepSteps.CountdownAllocationMoves
import SteppedFlapjack.PanToCrepSteps.RowColoring

/-! Staged graph coloring for the actual zero-count loop. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RegAlloc Flapjack.RiscV Flapjack.RiscV.CakeRegAlloc
open SteppedFlapjack.RegAllocSteps

def countdownZeroRendered := RowColoring.rendered countdownZeroLoopRow
def countdownZeroForced := RowColoring.forced countdownZeroLoopRow
def countdownZeroStackOnly := RowColoring.stackOnly countdownZeroLoopRow
def countdownZeroState := RowColoring.state countdownZeroLoopRow
def countdownZeroLimit := RowColoring.limit
def countdownZeroDecodedMoves := RowColoring.decoded countdownZeroLoopRow
def countdownZeroAdmitted := RowColoring.admitted countdownZeroLoopRow
def countdownZeroStart := RowColoring.start countdownZeroLoopRow
def countdownZeroCosts := RowColoring.costs countdownZeroLoopRow
def countdownZeroAllocated := RowColoring.allocated countdownZeroLoopRow
def countdownZeroPreferences := RowColoring.prefs countdownZeroLoopRow
def countdownZeroColoredA := RowColoring.coloredA countdownZeroLoopRow
def countdownZeroColored := RowColoring.colored countdownZeroLoopRow

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete allocator starts with a nine-step bound. -/
theorem countdownZero_allocation_fuel : countdownZeroStart.1 = 9 := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete coloring pass produces these exact node tags. -/
theorem countdownZero_colored_tags : countdownZeroColored.nodeTag.slots.toList =
    [some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),
      some (.fixed 1),some (.fixed 1),some (.fixed 0),some (.fixed 1),some (.fixed 0)] := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The concrete graph-coloring run does not report failure. -/
theorem countdownZero_colored_no_failure : countdownZeroColored.failure = none := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The actual source-to-allocator node numbering. -/
theorem countdownZero_bijection_exact : countdownZeroBijection.toAllocator =
    [(0,10),(13,9),(9,8),(25,7),(29,6),(33,5),(41,4),(21,3),(53,2),(2,1),(17,0)] := by
  with_unfolding_all rfl

/-- The extracted colors of the actual zero-count allocation. -/
theorem countdownZero_extracted_colors : cakeExtractColor countdownZeroColored countdownZeroBijection.toAllocator =
    [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)] := by
  have slots : countdownZeroColored.nodeTag.slots =
      #[some (.fixed 0),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),some (.fixed 1),
        some (.fixed 1),some (.fixed 1),some (.fixed 0),some (.fixed 1),some (.fixed 0)] := by
    apply Array.toList_inj.mp
    exact countdownZero_colored_tags
  rw [cakeExtractColor,countdownZero_bijection_exact]
  simp [cakeTagCol,CakeNodeMap.get,slots,List.mergeSort]

/-- The executable allocator returns this exact coloring for the actual
zero-count loop function. -/
theorem countdownZero_graphAllocation_exact :
    regAllocExecutable .IRC
      (WordAlloc.getHeuristics 3 countdownZeroLoopRow.1 countdownZeroAllocInput).2
      countdownZeroLimit countdownZeroMoves countdownZeroClashTree countdownZeroForced
      (WordAlloc.getStackOnly countdownZeroAllocInput) =
    .success (sptFromAList [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)]) := by
  have guard := countdown_zero_allocator_guard
  rw [countdownZeroLoopRow_from_compiler] at guard
  have accepted : countdownAllocatorGuard countdownZeroLoopRow = true := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,true_and,and_true] using guard
  exact RowColoring.graphAllocation_exact countdownZeroLoopRow _ accepted
    countdownZero_colored_no_failure countdownZero_extracted_colors

/-- The exact register coloring computed by the graph allocator. -/
def countdownZeroColor : Spt Nat :=
  sptFromAList [(0,0),(2,1),(9,0),(13,1),(17,0),(21,1),(25,1),(29,1),(33,1),(41,1),(53,1)]

set_option maxHeartbeats 1000000 in
/-- The exact graph coloring is applied in the actual loop compilation. -/
theorem countdownZero_compiledLoop_exact :
    WordToWord.fullCompileSingleWith regAllocExecutable
      riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig (countdownZeroLoopRow,none) =
      (countdownZeroLoopRow.1,countdownZeroLoopRow.2.1,
        WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour countdownZeroColor) countdownZeroAllocInput)) := by
  have guard := countdown_zero_allocator_guard
  rw [countdownZeroLoopRow_from_compiler] at guard
  have accepted : countdownAllocatorGuard countdownZeroLoopRow = true := by
    simpa only [List.map_cons,List.map_nil,List.cons.injEq,true_and,and_true] using guard
  exact RowColoring.compiled_exact countdownZeroLoopRow _ accepted
    countdownZero_colored_no_failure countdownZero_extracted_colors

/-- The exact optimized Word functions with the entry and loop allocations. -/
def countdownZeroOptimizedWord : List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  [WordToWord.fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit 3 riscvConfig
      ((64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),none),
   (countdownZeroLoopRow.1,countdownZeroLoopRow.2.1,
    WordRemove.removeMustTerminate (WordAlloc.applyColour (WordAlloc.totalColour countdownZeroColor) countdownZeroAllocInput))]

/-- The full Word compiler returns the exact optimized countdown functions. -/
theorem countdownZero_optimizedWord_exact :
    (WordToWord.compileWith regAllocExecutable countdownRiscVBackend.wordToWordConf riscvConfig
      (panToWordCompileProgHOL riscvConfig.isa
        (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main")
          (.dec (Flapjack.Basis.Pure.MlString.ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (Flapjack.Basis.Pure.MlString.ofString "x"))
              (.assign .local (Flapjack.Basis.Pure.MlString.ofString "x")
                (.op .sub [.var .local (Flapjack.Basis.Pure.MlString.ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2 = countdownZeroOptimizedWord := by
  rw [countdownWordLiteral_zero_eq]
  have hwords : countdownWordLiteral 0 0 =
      [(64,1,.seq .skip (.seq (.call none (some 65) [0] none) .skip)),countdownZeroLoopRow] := rfl
  rw [hwords]
  have horacle : countdownRiscVBackend.wordToWordConf.colOracle = [] := rfl
  have halg : countdownRiscVBackend.wordToWordConf.regAlg = 3 := rfl
  simp only [WordToWord.compileWith,horacle,halg]
  change [_,WordToWord.fullCompileSingleWith regAllocExecutable riscvConfig.twoRegArith countdownZeroLimit
    3 riscvConfig (countdownZeroLoopRow,none)] = _
  rw [countdownZero_compiledLoop_exact]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The actual label-removal pass succeeds and emits exactly 1040 bytes for
the zero-count program. -/
theorem countdownZero_removeLabels_size :
    (LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (countdownStackLabCode (ofString "x") 0 0 countdownRiscVBackend))).map
        (fun (code,_) => (LabToTarget.progToBytes code).length) = some 1040 := by
  unfold countdownStackLabCode countdownNativeRiscV
  rw [← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
  rw [countdownZero_optimizedWord_exact]
  simp_rw [LabToTarget.progToBytesMap]
  with_unfolding_all decide

/-- The actual full compiler succeeds on the zero-count program, and its
emitted bytecode fits in the concrete machine memory layout. -/
theorem countdownZero_compilation_fits :
    ∃ bytes final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
        (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
        (.return (.const (0 : BitVec 64))))))) = some (bytes,[4],final) ∧ bytes.length ≤ 1040 := by
  apply (countdown_artifact_bounded_iff_removeLabels (ofString "x") 0 0 1040).2
  have size := countdownZero_removeLabels_size
  cases h : LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (countdownStackLabCode (ofString "x") 0 0 countdownRiscVBackend)) with
  | none => simp only [h,Option.map_none] at size; cases size
  | some result =>
    rcases result with ⟨code,labs⟩
    refine ⟨code,labs,rfl,?_⟩
    simp only [h,Option.map_some,Option.some.injEq] at size
    omega

end SteppedFlapjack.PanToCrepSteps
